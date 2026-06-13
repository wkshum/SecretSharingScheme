import Mathlib.Tactic

-- We need Lagrange interpolation in Shamir's scheme
import Mathlib.LinearAlgebra.Lagrange

-- import AccessStructure and SecretSharing Scheme
import SecretSharingScheme.section_1_AccessStructure
import SecretSharingScheme.section_2_SecretSharingScheme



noncomputable section ShamirScheme

namespace ShamirScheme

open AccessStructure
open SecretSharingScheme
open BigOperators Finset Matrix Polynomial
open scoped Classical

/-
Definition of the polynomial used in Shamir's Secret Sharing Scheme.
-/
universe u

-- Declare F as a finite field
variable {F : Type*} [Field F] [Fintype F]

/-- Shamir's secret sharing polynomial evaluation.
    s is the secret (constant term).
    m contains the t-1 random coefficients m_1, ..., m_{t-1}.
    z is the evaluation point. -/
def shamir_poly (t : ℕ) (s : F) (m : Fin (t - 1) → F) (z : F) : F :=
  s + ∑ j : Fin (t - 1), m j * z ^ (j.val + 1)

/-
The uniform distribution on the coefficients.
-/
noncomputable def uniform_coeffs (t : ℕ) : PMF (Fin (t - 1) → F) :=
  PMF.uniformOfFintype (Fin (t - 1) → F)

/-
The cardinality of a finite field is at least 2.
-/
theorem FiniteField.card_ge_two (F : Type*) [Field F] [Fintype F] : Fintype.card F ≥ 2 := by
  have h : 0 ≠ (1 : F) := zero_ne_one
  have h_card : Fintype.card F > 1 := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  exact Nat.succ_le_of_lt h_card

/-- Shamir's Secret Sharing Scheme. -/
def shamirScheme (n t : ℕ)
    (x : Fin n → F)
    (_h_distinct : Function.Injective x)
    (_h_nonzero : ∀ i, x i ≠ 0) : SecretSharingScheme n where
  Secret := F
  Random := Fin (t - 1) → F
  hSecret := inferInstance
  hSecret_card := FiniteField.card_ge_two F
  Share := fun _ => F
  hShare := fun _ => inferInstance
  hRandom := inferInstance
  hRandomNonempty := inferInstance
  μ := uniform_coeffs t
  dealer := fun s m i => shamir_poly t s m (x i)


theorem threshold_auth_iff (n t : ℕ) (B : Set (Fin n)) :
    B ∈ (thresholdAccessStructure n t).auth ↔ t ≤ B.ncard := by
  -- By definition of the threshold access structure, B is authorized if and only if there exists a subset A with exactly t elements such that A is a subset of B.
  simp [thresholdAccessStructure, generatedAccessStructure];
  -- If there exists a subset $a$ of $B$ with cardinality $t$, then clearly $t \leq B.ncard$.
  apply Iff.intro;
  · rintro ⟨ a, ha₁, ha₂ ⟩ ; exact ha₁ ▸ Set.ncard_le_ncard ha₂;
  · -- If B has at least t elements, then we can choose a subset a of B with exactly t elements.
    intro ht
    obtain ⟨a, ha⟩ : ∃ a : Finset (Fin n), a.card = t ∧ ∀ x ∈ a, x ∈ B := by
      have := Set.exists_subset_card_eq ht;
      obtain ⟨ a, ha₁, ha₂ ⟩ := this; exact ⟨ a.toFinset, by simpa [ Set.ncard_eq_toFinset_card' ] using ha₂, fun x hx => ha₁ <| by simpa using hx ⟩ ;
    exact ⟨ a, by simpa [ Set.ncard_eq_toFinset_card' ] using ha.1, fun x hx => ha.2 x hx ⟩

noncomputable def shamir_reconstruction (n t : ℕ) (x : Fin n → F)
    (B : Set (Fin n)) (hB : B ∈ (thresholdAccessStructure n t).auth)
    (shares : (i : B) → F) : F :=
  let h_card : t ≤ B.ncard := (threshold_auth_iff n t B).mp hB
  let S := Classical.choose (Set.exists_subset_card_eq h_card)
  let S_finset := S.toFinset
  let shares_ext : Fin n → F := fun i =>
    if h : i ∈ B then shares ⟨i, h⟩ else 0
  ((Lagrange.interpolate S_finset x) shares_ext).eval 0

def shamir_linear_map (n t : ℕ) (x : Fin n → F) (B : Set (Fin n)) (r : Fin (t - 1) → F) : B → F :=
  fun i => ∑ j : Fin (t - 1), r j * (x i) ^ (j.val + 1)

lemma shamir_linear_map_surjective (n t : ℕ)
  (x : Fin n → F) (h_distinct : Function.Injective x)
    (h_nonzero : ∀ i, x i ≠ 0) (B : Set (Fin n)) (hB : B.ncard < t) :
    Function.Surjective (shamir_linear_map n t x B) := by
  -- Since $B$ has fewer than $t$ elements,
  -- the system of equations given by the evaluations is underdetermined,
  -- and thus there exists a $p$ such that $p(i) = s_i$ for each $i \in B$.
  have h_undetermined : ∀ (s : B → F), ∃ p : Fin (t - 1) → F, ∀ i : B, ∑ j : Fin (t - 1), p j * x i ^ (j.val + 1) = s i := by
    -- Since the Vandermonde matrix is invertible,
    -- the system of equations has a unique solution for any right-hand side.
    have h_vandermonde_inv : ∀ (s : B → F), ∃ p : Fin (B.ncard) → F, ∀ i : B, ∑ j : Fin (B.ncard), p j * x i ^ (j.val + 1) = s i := by
      -- Since the x_i are distinct, the Vandermonde matrix is invertible,
      -- so the system has a unique solution.
      have h_vandermonde_inv : ∀ (s : B → F), ∃ p : Fin (B.ncard) → F,
          ∀ i : B, ∑ j : Fin (B.ncard), p j * x i ^ (j.val) = s i := by
        intro s;
        -- Since $B$ is a finite set, we can choose a bijection $f : Fin B.ncard ≃ B$.
        obtain ⟨f, hf⟩ : ∃ f : Fin B.ncard ≃ B, True := by
          simp +zetaDelta at *;
          exact ⟨ Fintype.equivOfCardEq <| by simp  [ Set.ncard_eq_toFinset_card' ] ⟩;
        -- Since $B$ is a finite set, we can choose a bijection $f : Fin B.ncard ≃ B$ and use it to construct the polynomial $p$.
        obtain ⟨p, hp⟩ : ∃ p : Fin B.ncard → F, ∀ i : Fin B.ncard, ∑ j : Fin B.ncard, p j * x (f i) ^ (j.val) = s (f i) := by
          have h_vandermonde_inv : Matrix.det (Matrix.of (fun i j : Fin B.ncard => x (f i) ^ (j.val))) ≠ 0 := by
            erw [ Matrix.det_vandermonde ];
            simp  [ Finset.prod_eq_zero_iff, sub_eq_zero, h_distinct.eq_iff ];
            exact fun i j hij => fun h => hij.ne <| f.injective <| Subtype.ext h.symm;
          have h_vandermonde_inv : ∀ (b : Fin B.ncard → F), ∃ p : Fin B.ncard → F, Matrix.mulVec (Matrix.of (fun i j : Fin B.ncard => x (f i) ^ (j.val))) p = b := by
            exact fun b => ⟨ Matrix.mulVec ( Matrix.of ( fun i j : Fin B.ncard => x ( f i ) ^ ( j.val ) ) ) ⁻¹ b, by simp  [ h_vandermonde_inv, isUnit_iff_ne_zero ] ⟩;
          exact Exists.elim ( h_vandermonde_inv fun i => s ( f i ) ) fun p hp => ⟨ p, fun i => by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hp i ⟩;
        exact ⟨ p, fun i => by simpa using hp ( f.symm i ) |> fun h => by simpa [ f.apply_symm_apply ] using h ⟩;
      intro s
      obtain ⟨p, hp⟩ := h_vandermonde_inv (fun i => s i / x i);
      use p;
      simp_all  [ pow_succ, ← mul_assoc, ← Finset.sum_mul _ _ _ ];
    intro s
    obtain ⟨p, hp⟩ := h_vandermonde_inv s;
    use fun j => if hj : j.val < B.ncard then p ⟨ j.val, hj ⟩ else 0;
    intro i;
    rw [ ← hp i ] ;
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun j : Fin B.ncard => ⟨ j.val, by linarith [ Fin.is_lt j, Nat.sub_add_cancel ( show 1 ≤ t from Nat.succ_le_of_lt ( pos_of_gt hB ) ) ] ⟩ : Fin B.ncard → Fin ( t - 1 ) ) Finset.univ ) ) ] ;
    · -- rw [ Finset.sum_image ] <;>
      --simp [ Fin.ext_iff ];
      simp only [dite_mul, zero_mul, coe_univ, Fin.ext_iff, implies_true, Set.injOn_of_eq_iff_eq, sum_image, Fin.is_lt,
    ↓reduceDIte, Fin.eta]
    simp +contextual [ Fin.ext_iff ];
      exact fun j hj h => False.elim <| hj ⟨ j, h ⟩ rfl;
  exact fun s => by obtain ⟨ p, hp ⟩ := h_undetermined s; exact ⟨ p, funext fun i => by simpa [ shamir_poly ] using hp i ⟩ ;

lemma map_uniform_of_fiber_card_eq {A B : Type u} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B) (k : ℕ) (h_fibers : ∀ y : B, Fintype.card {x // f x = y} = k) :
    PMF.map f (PMF.uniformOfFintype A) = PMF.uniformOfFintype B := by
  -- By definition of PMF.map, we have:
  ext y
  simp [PMF.map];
  -- Since there are $k$ elements in $A$ that map to $y$, the sum of the probabilities of these elements is $k \cdot \frac{1}{|A|} = \frac{k}{|A|}$.
  have h_sum : ∑' a : A, (if y = f a then (1 : ENNReal) / (Fintype.card A) else 0) = (k : ENNReal) / (Fintype.card A) := by
    rw [ tsum_eq_sum ];
    any_goals exact Finset.univ.filter fun x => f x = y;
    · simp  [ ← h_fibers y, Fintype.card_subtype ];
      rw [ Finset.sum_congr rfl fun x hx => if_pos <| Eq.symm <| Finset.mem_filter.mp hx |>.2 ] ; simp  [ div_eq_mul_inv ];
    · aesop;
  -- Since there are $k$ elements in $A$ that map to each $y$, the total number of elements in $A$ is $k \cdot |B|$.
  have h_card_A : Fintype.card A = k * Fintype.card B := by
    have h_card_A : Fintype.card A = ∑ y : B, Fintype.card { x : A // f x = y } := by
      simp  only [Fintype.card_subtype];
      simp  only [Finset.card_filter];
      rw [ Finset.sum_comm ] ; simp ;
    simp  [ h_card_A, h_fibers, mul_comm ];
  by_cases hk : k = 0 <;> simp_all  [ division_def ];
  rw [←  ENNReal.toReal_eq_toReal_iff' ] <;> norm_num [ hk ];
  · exact mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr hk );
  · simp  [ ENNReal.mul_eq_top, hk ]

lemma shamir_fiber_card_constant (n t : ℕ) (x : Fin n → F)
  (h_distinct : Function.Injective x)
    (h_nonzero : ∀ i, x i ≠ 0) (B : Set (Fin n)) (hB : B.ncard < t) (s : F) :
    ∃ k, ∀ y : B → F, Fintype.card { m : Fin (t - 1) → F // (fun i : B => shamir_poly t s m (x i)) = y } = k := by
  use Fintype.card { m : Fin (t - 1) → F // (fun i : B => shamir_poly t s m (x i)) = (fun i : B => shamir_poly t s 0 (x i)) };
  intro y
  have h_fibers : ∀ y : B → F, ∃ m₀ : Fin (t - 1) → F, (fun i : B => shamir_poly t s m₀ (x i)) = y := by
    intro y
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Fin (t - 1) → F, (fun i : B => ∑ j : Fin (t - 1), m₀ j * (x i) ^ (j.val + 1)) = fun i : B => y i - s := by
      have := shamir_linear_map_surjective n t x h_distinct h_nonzero B hB;
      exact this _;
    use m₀; simp_all  [ funext_iff, shamir_poly ] ;
  obtain ⟨ m₀, rfl ⟩ := h_fibers y;
  refine' Fintype.card_congr _;
  refine' ⟨ fun m => ⟨ m.val - m₀, _ ⟩, fun m => ⟨ m.val + m₀, _ ⟩, fun m => _, fun m => _ ⟩ <;> simp_all  [ funext_iff];
  · intro i hi; have := congr_fun m.2 ⟨ i, hi ⟩ ; simp_all  [ shamir_poly ] ;
    simp_all  [ sub_mul ];
  · intro i hi; have := congr_fun m.2 ⟨ i, hi ⟩ ; simp_all  [ shamir_poly ] ;
    simp_all  [ add_mul, Finset.sum_add_distrib ]

lemma shamir_shares_uniform (n t : ℕ)
    (x : Fin n → F) (h_distinct : Function.Injective x) (h_nonzero : ∀ i, x i ≠ 0)
    (B : Set (Fin n)) (hB : B.ncard < t) (s : F) :
    PMF.map (fun r => fun (i : B) => shamir_poly t s r (x i)) (uniform_coeffs t) = PMF.uniformOfFintype (B → F) := by
  apply map_uniform_of_fiber_card_eq;
  convert shamir_fiber_card_constant n t x h_distinct h_nonzero B hB s |> Classical.choose_spec

theorem shamir_perfect_security (n t : ℕ)
    (x : Fin n → F) (h_distinct : Function.Injective x) (h_nonzero : ∀ i, x i ≠ 0) :
    PerfectSecurity (shamirScheme n t x h_distinct h_nonzero)
      (thresholdAccessStructure n t) := by
        intro B hB s s';
        have h_uniform : ∀ s : F, PMF.map (fun r : Fin (t - 1) → F => fun (i : B)
          => shamir_poly t s r (x i))
          (uniform_coeffs t) = PMF.uniformOfFintype (B → F) := by
          apply shamir_shares_uniform;
          --· exact (FiniteField.card_ge_two F);
          · assumption;
          · assumption;
          · exact lt_of_not_ge fun h => hB <| threshold_auth_iff n t B |>.2 h;
        exact h_uniform s ▸ h_uniform s' ▸ rfl

-- alternate description of shamir_poly using Polynomial type
def shamir_polynomial (t : ℕ) (s : F) (m : Fin (t - 1) → F) : Polynomial F :=
  Polynomial.C s + ∑ i : Fin (t - 1), Polynomial.C (m i) * Polynomial.X ^ (i.val + 1)

-- shamir_poly and shamir_polynomial have the same mathematical meaning
lemma shamir_polynomial_eval (t : ℕ) (s : F) (m : Fin (t - 1) → F) (z : F) :
    (shamir_polynomial t s m).eval z = shamir_poly t s m z := by
      -- By definition of polynomial evaluation, we can expand the left-hand side.
      simp [shamir_polynomial, Polynomial.eval_finset_sum, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow];
      -- By definition of polynomial evaluation, we can expand the left-hand side to match the right-hand side.
      simp [shamir_poly]

-- Shamir polynomial has degree less the or equal to t-1
lemma shamir_polynomial_degree_le (t : ℕ) (s : F) (m : Fin (t - 1) → F) :
    (shamir_polynomial t s m).natDegree ≤ t - 1 := by
      -- The polynomial is constructed by adding a constant term s and a sum of terms m_i * x^(i+1). Each term in the sum is a monomial of degree i+1, where i ranges from 0 to t-2. The highest degree term here is when i is t-2, which gives x^(t-1). So the degree of the polynomial should be t-1.
      have h_deg : (shamir_polynomial t s m).natDegree ≤ Finset.sup (Finset.univ : Finset (Fin (t - 1))) (fun i => i.val + 1) := by
        -- The degree of the sum of polynomials is the maximum of their degrees.
        have h_deg_sum : (Finset.sum Finset.univ fun i => Polynomial.C (m i) * Polynomial.X ^ ((i : ℕ) + 1)).natDegree ≤ Finset.sup (Finset.univ : Finset (Fin (t - 1))) (fun i => (i : ℕ) + 1) := by
          refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ );
          exact fun i _ => le_trans ( Polynomial.natDegree_C_mul_X_pow_le _ _ ) ( Finset.le_sup ( f := fun i : Fin ( t - 1 ) => ( i : ℕ ) + 1 ) ( Finset.mem_univ i ) );
        exact le_trans ( Polynomial.natDegree_add_le _ _ ) ( max_le ( by aesop ) h_deg_sum );
      exact h_deg.trans ( Finset.sup_le fun i _ => Nat.succ_le_of_lt i.2 )

-- Prove that the interpoloation formula for reconstruction is correct
lemma shamir_interpolation_correct (n t : ℕ)
    (x : Fin n → F) (h_distinct : Function.Injective x) (_h_nonzero : ∀ i, x i ≠ 0)
    (s : F) (m : Fin (t - 1) → F)
    (B : Set (Fin n)) (hB : B ∈ (thresholdAccessStructure n t).auth) (ht : t ≠ 0) :
    let h_card : t ≤ B.ncard := (threshold_auth_iff n t B).mp hB
    let S := Classical.choose (Set.exists_subset_card_eq h_card)
    let S_finset := S.toFinset
    let shares : (i : B) → F := fun i => shamir_poly t s m (x i)
    let shares_ext : Fin n → F := fun i => if h : i ∈ B then shares ⟨i, h⟩ else 0
    (Lagrange.interpolate S_finset x) shares_ext = shamir_polynomial t s m := by
      refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
      · exact Finset.image x ( Classical.choose ( Set.exists_subset_card_eq ( show t ≤ B.ncard from ( threshold_auth_iff n t B ).mp hB ) ) |> Set.toFinset );
      · refine' lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) ( max_lt _ _ );
        · convert Lagrange.degree_interpolate_lt _ _;
          · rw [ Finset.card_image_of_injective _ h_distinct ];
          · exact h_distinct.injOn;
        · refine' lt_of_le_of_lt ( Polynomial.degree_le_natDegree ) _;
          rw [ Finset.card_image_of_injective _ h_distinct ];
          have := Classical.choose_spec ( Set.exists_subset_card_eq ( show t ≤ Set.ncard B from ( threshold_auth_iff n t B ).mp hB ) );
          simp_all  [ Set.ncard_eq_toFinset_card' ];
          exact lt_of_le_of_lt ( shamir_polynomial_degree_le t s m ) ( Nat.pred_lt ht );
      · simp;
        intro i hi; rw [ Polynomial.eval_finset_sum, Finset.sum_eq_single i ] <;> simp  [ Lagrange.basis ] ;
        · rw [ if_pos ( Classical.choose_spec ( Set.exists_subset_card_eq ( show t ≤ B.ncard from ( threshold_auth_iff n t B ).mp hB ) ) |>.1 hi ) ] ; simp  [ Polynomial.eval_prod, Lagrange.basisDivisor ] ;
          rw [ Finset.prod_eq_one fun j hj => by rw [ inv_mul_cancel₀ ] ; exact sub_ne_zero_of_ne <| h_distinct.ne <| by aesop ] ; simp  [ shamir_polynomial_eval ];
        · intro j hj hij hjB; rw [ Polynomial.eval_prod ] ; exact Or.inr ( Finset.prod_eq_zero ( Finset.mem_erase_of_ne_of_mem ( Ne.symm hij ) ( by aesop ) ) ( by simp  [ Lagrange.basisDivisor ] ) ) ;
        · exact fun h₁ h₂ => False.elim <| h₁ hi

-- Correctness of Shamir secret sharing scheme
theorem shamir_scheme_correctness (n t : ℕ)
    (x : Fin n → F) (h_distinct : Function.Injective x) (h_nonzero : ∀ i, x i ≠ 0) (ht : t ≠ 0) :
    Correctness (shamirScheme n t x h_distinct h_nonzero)
      (thresholdAccessStructure n t) (shamir_reconstruction n t x) := by
        -- By definition of Shamir's scheme, the polynomial is constructed such that evaluating it at 0 gives the secret.
        have h_poly_eval : ∀ (s : F) (m : Fin (t - 1) → F), (shamir_polynomial t s m).eval 0 = s := by
          -- By definition of Shamir's polynomial, evaluating it at 0 gives the secret.
          intros s m
          simp [shamir_polynomial];
          simp  [ Polynomial.eval_finset_sum ];
        intro s r B hB;
        convert h_poly_eval s r using 1;
        convert congr_arg ( Polynomial.eval 0 ) ( shamir_interpolation_correct n t x h_distinct h_nonzero s r B hB ht ) using 1


-- Shamir secret sharing scheme realizes threshold access structure
def shamirRealizedScheme (n t : ℕ)
    (x : Fin n → F) (h_distinct : Function.Injective x) (h_nonzero : ∀ i, x i ≠ 0)
    (ht : t > 0)
  : RealizedSecretSharingScheme n (thresholdAccessStructure n t) := {
  shamirScheme n t x h_distinct h_nonzero with
  recon := shamir_reconstruction n t x
  h_correctness := shamir_scheme_correctness n t x h_distinct h_nonzero (ne_of_gt ht)
  h_security := shamir_perfect_security n t x h_distinct h_nonzero
}

end ShamirScheme  -- namespace

end ShamirScheme  --section
