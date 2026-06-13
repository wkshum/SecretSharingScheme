import Mathlib.Tactic

import SecretSharingScheme.section_1_AccessStructure
import SecretSharingScheme.section_2_SecretSharingScheme


section DisjointAccessStructure

open AccessStructure

open BigOperators
open Classical
variable {n : ℕ} {p : ℕ} [Fact p.Prime]


/--
A share is an optional value in ZMod p.
If the participant is not in any qualified set, it is none.
-/
def Share (p : ℕ) := Option (ZMod p)

/--
The validity of a sharing of a secret S with respect to the disjoint qualified sets Qs.
-/
def IsValidSharing (Qs : Set (Set (Fin n))) (S : ZMod p) (σ : Fin n → Share p) : Prop :=
  -- 1. Participants not in any Q ∈ Qs have no share.
  (∀ i, (∀ Q ∈ Qs, i ∉ Q) → σ i = none) ∧
  -- 2. Participants in some Q ∈ Qs have a share.
  (∀ Q ∈ Qs, ∀ i ∈ Q, (σ i).isSome) ∧
  -- 3. For each Q ∈ Qs, the sum of shares is S.
  (∀ Q ∈ Qs, (∑ i : Fin n, if i ∈ Q then ((σ i).getD 0) else 0) = S)

/--
Generate shares for a secret S using random values ρ.
For each Q ∈ Qs, we use the max element to balance the sum.
-/
noncomputable def GenerateShares (Qs : Set (Set (Fin n))) (S : ZMod p) (ρ : Fin n → ZMod p) : Fin n → Share p := fun i =>
  if h : ∃ Q ∈ Qs, i ∈ Q then
    let Q := Classical.choose h
    have hQ_spec : Q ∈ Qs ∧ i ∈ Q := Classical.choose_spec h
    have h_finite : Q.Finite := Set.toFinite Q
    let Q_finset := h_finite.toFinset
    have h_nonempty : Q_finset.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact ⟨i, hQ_spec.2⟩
    let last := Q_finset.max' h_nonempty
    if i = last then
      -- Sum of random values assigned to other members of Q
      let others := Q_finset.erase last
      let sum_others := ∑ j ∈ others, ρ j
      some (S - sum_others)
    else
      some (ρ i)
  else
    none

/--
Reconstruct the secret from a set of participants G and their shares.
If G contains a qualified set Q, we sum the shares of Q.
-/
noncomputable def ReconstructSecret (Qs : Set (Set (Fin n))) (shares : Fin n → Share p) (G : Set (Fin n)) : Option (ZMod p) :=
  if h : ∃ Q ∈ Qs, Q ⊆ G then
    let Q := Classical.choose h
    -- We sum the shares of members of Q.
    -- We assume shares are present (if not, getD 0 will return 0, which might be wrong, but for valid shares it's fine).
    let sum_shares := ∑ i ∈ (Set.toFinite Q).toFinset, (shares i).getD 0
    some sum_shares
  else
    none

/-
Definition of pivot: selects an element in Q \ A to adjust if the last element is in A.
-/
noncomputable def pivot (Q : Set (Fin n)) (A : Set (Fin n)) : Option (Fin n) :=
  if hQ : Q.Nonempty then
    let last := (Set.toFinite Q).toFinset.max' ((Set.toFinite Q).toFinset_nonempty.mpr hQ)
    if last ∈ A then
      if h_diff : ∃ x, x ∈ Q ∧ x ∉ A then
        some (Classical.choose h_diff)
      else
        none
    else
      none
  else
    none

/-
Definition of shift: the adjustment vector for the random tape.
-/
noncomputable def shift (Qs : Set (Set (Fin n))) (A : Set (Fin n)) (S1 S2 : ZMod p) (i : Fin n) : ZMod p :=
--  S2 - S1
  if _h : ∃ Q ∈ Qs, pivot Q A = some i then
    S2 - S1
  else
    0

/-
Lemma: pivot returns some value iff the last element of Q is in A.
-/
theorem pivot_spec {Q : Set (Fin n)} {A : Set (Fin n)} (hQ : Q.Nonempty) (h_unauth : ¬(Q ⊆ A)) :
  (pivot Q A).isSome ↔ ((Set.toFinite Q).toFinset.max' ((Set.toFinite Q).toFinset_nonempty.mpr hQ)) ∈ A := by
    unfold pivot;
    split_ifs <;> simp_all +decide [ Set.subset_def ]

/-
Lemma: if pivot returns x, then x is in Q, not in A, and not the last element.
-/
theorem pivot_mem {Q : Set (Fin n)} {A : Set (Fin n)} (hQ : Q.Nonempty) (x : Fin n) :
  pivot Q A = some x → x ∈ Q ∧ x ∉ A ∧ x ≠ (Set.toFinite Q).toFinset.max' ((Set.toFinite Q).toFinset_nonempty.mpr hQ) := by
    intros hx;
    unfold pivot at hx;
    split_ifs at hx ;
    · simp_all [ Finset.max'_eq_sup' ];
      · have := Classical.choose_spec ‹∃ x ∈ Q, x∉A›;
        aesop;
    · grind

/-
Lemma: The shift vector is zero for any participant in the unauthorized set A.
-/
theorem shift_eq_zero_on_A {Qs : Set (Set (Fin n))} {A : Set (Fin n)} {S1 S2 : ZMod p}
    (_h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (i : Fin n) (hi : i ∈ A) :
    shift Qs A S1 S2 i = 0 := by
  unfold shift

  split_ifs with h
  · obtain ⟨Q, hQ, h_pivot⟩ := h
    -- pivot Q A = some i implies i ∉ A
    have := pivot_mem (h_nonempty Q hQ) i h_pivot
    have hi_not_A := this.2.1
    contradiction
  · rfl

/-
Lemma: For a qualified set Q where the last element is in A, the sum of shifts on the other elements is S2 - S1.
-/
theorem sum_shift_eq_diff {Qs : Set (Set (Fin n))} {A : Set (Fin n)} {S1 S2 : ZMod p}
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (h_unauth : ∀ Q ∈ Qs, ¬(Q ⊆ A))
    (Q : Set (Fin n)) (hQ : Q ∈ Qs)
    (last : Fin n) (h_last : last = (Set.toFinite Q).toFinset.max' ((Set.toFinite Q).toFinset_nonempty.mpr (h_nonempty Q hQ)))
    (h_last_in_A : last ∈ A) :
    ∑ j ∈ (Set.toFinite Q).toFinset.erase last, shift Qs A S1 S2 j = S2 - S1 := by
  -- The sum has only one non-zero term, corresponding to the pivot.
  -- pivot Q A is some x, with x ∈ Q \ A.
  -- Since last ∈ A, x ≠ last.
  -- So x ∈ (Q \ {last}).
  -- Also shift is zero everywhere else in Q (because Qs are disjoint).
  have h_shift_def : ∀ j ∈ (Set.toFinite Q).toFinset.erase last, shift Qs A S1 S2 j = if pivot Q A = some j then S2 - S1 else 0 := by
    intro j hj;
    convert if_congr ?_ rfl rfl;
    constructor;
    · rintro ⟨ Q', hQ', h ⟩;
      have h_eq : Q' = Q := by
        have h_eq : j ∈ Q' ∧ j ∈ Q := by
          have := pivot_mem ( h_nonempty Q' hQ' ) j h; aesop;
        have := h_disjoint hQ' hQ;
        exact Classical.not_not.1 fun h => Set.disjoint_left.mp ( this h ) h_eq.1 h_eq.2;
      aesop;
    · exact fun h => ⟨ Q, hQ, h ⟩;
  have h_pivot_def : ∃ x, pivot Q A = some x ∧ x ∈ (Set.toFinite Q).toFinset.erase last := by
    unfold pivot;
    simp_all +decide [ Set.not_subset ];
    exact ⟨ fun h => Classical.choose_spec ( h_unauth Q hQ ) |>.2 <| h ▸ h_last_in_A, Classical.choose_spec ( h_unauth Q hQ ) |>.1 ⟩;
  obtain ⟨ x, hx₁, hx₂ ⟩ := h_pivot_def;
  rw [ Finset.sum_eq_single x ] <;> aesop

/-
Lemma: shift(S2, S1) is the negation of shift(S1, S2).
-/
theorem shift_symm {Qs : Set (Set (Fin n))} {A : Set (Fin n)} {S1 S2 : ZMod p} :
    shift Qs A S2 S1 = - shift Qs A S1 S2 := by
      -- By definition of shift, we have that shift Qs A S2 S1 i = S2 - S1 if there exists a Q in Qs such that pivot Q A is some i, otherwise 0.
      funext i; simp [shift];
      split_ifs <;> ring

/-
Lemma: The generated shares for S2 using the shifted random tape are the same as for S1 using the original tape, for participants in A.
-/
theorem generateShares_shift_eq {Qs : Set (Set (Fin n))} {A : Set (Fin n)} {S1 S2 : ZMod p}
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (h_unauth : ∀ Q ∈ Qs, ¬(Q ⊆ A))
    (ρ : Fin n → ZMod p)
    (i : Fin n) (hi : i ∈ A) :
    GenerateShares Qs S2 (ρ + shift Qs A S1 S2) i =
    GenerateShares Qs S1 ρ i := by
  -- By definition of GenerateShares, we need to consider three cases: when Q contains i, when Q does not contain i, and when Q is not in Qs.
  by_cases hQ : ∃ Q ∈ Qs, i ∈ Q;
  · -- Since $i \in A$, we have $shift Qs A S1 S2 i = 0$ by definition of shift.
    have h_shift_zero : shift Qs A S1 S2 i = 0 := by
      exact shift_eq_zero_on_A h_disjoint h_nonempty i hi;
    -- Since $shift Qs A S1 S2 i = 0$, adding it to $\rho$ does not change the value.
    simp [h_shift_zero, GenerateShares];
    split_ifs <;> simp [ Finset.sum_add_distrib ];
    convert sum_shift_eq_diff h_disjoint h_nonempty h_unauth _ _ _ rfl using 1;
    rotate_left;
    · exact p;
    · exact ⟨ Fact.out ⟩;
    · exact S1;
    · exact S2;
    · exact Classical.choose hQ;
    · exact Classical.choose_spec hQ |>.1;
    simp +decide [ ← ‹i = _›];
    grind;
  · -- Since there's no Q in Qs containing i, by definition of GenerateShares, both shares should be none. So, the equality holds trivially because both sides are none.
    simp [GenerateShares, hQ]



/-
Lemma: The shift map is a bijection.
-/
theorem shift_is_bijection {Qs : Set (Set (Fin n))} {A : Set (Fin n)} {S1 S2 : ZMod p}
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (h_unauth : ∀ Q ∈ Qs, ¬(Q ⊆ A))
    (shares_A : ∀ i : Fin n, i ∈ A → Share p) :
    Set.BijOn (fun ρ => ρ + shift Qs A S1 S2)
      {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S1 ρ i = shares_A i hi}
      {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S2 ρ i = shares_A i hi} := by
        refine' ⟨ fun ρ hρ i hi => _, _, _ ⟩;
        · convert generateShares_shift_eq h_disjoint h_nonempty h_unauth ρ i hi using 1;
          exact hρ i hi ▸ rfl;
        · exact fun x hx y hy hxy => by simpa using hxy;
        · intro ρ hρ;
          refine' ⟨ ρ - shift Qs A S1 S2, _, _ ⟩ <;> simp_all +decide [ sub_eq_add_neg ];
          convert generateShares_shift_eq h_disjoint h_nonempty h_unauth ( ρ + -shift Qs A S1 S2 ) using 1;
          rotate_left;
          · exact S1;
          · exact S2;
          · simp +decide [ ← hρ ];
            rw [ eq_comm ]


/-
Perfect security theorem: The number of random tapes consistent with a given set of shares on an unauthorized set is independent of the secret.
-/
theorem PerfectSecurity {n : ℕ} {p : ℕ} [Fact p.Prime]
    (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (A : Set (Fin n))
    (h_unauth : ∀ Q ∈ Qs, ¬(Q ⊆ A)) -- A is unauthorized
    (shares_A : ∀ i : Fin n, i ∈ A → Share p) -- Fixed shares for A
    (S1 S2 : ZMod p) :
    Set.ncard {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S1 ρ i = shares_A i hi} =
    Set.ncard {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S2 ρ i = shares_A i hi} := by
      -- the shift map is a bijection.
      have h_bijection : Set.BijOn (fun ρ => ρ + shift Qs A S1 S2)
        {ρ : Fin n → ZMod p | ∀ i hi, GenerateShares Qs S1 ρ i = shares_A i hi}
        {ρ : Fin n → ZMod p | ∀ i hi, GenerateShares Qs S2 ρ i = shares_A i hi} := by
          exact shift_is_bijection h_disjoint h_nonempty h_unauth shares_A
      rw [ Set.ncard_def, Set.ncard_def, Set.encard_congr ( h_bijection.equiv ) ]

/-
Perfect security theorem
-/
theorem PerfectSecurity_thm {n : ℕ} {p : ℕ} [Fact p.Prime]
    (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (A : Set (Fin n))
    (h_unauth : ∀ Q ∈ Qs, ¬(Q ⊆ A)) -- A is unauthorized
    (shares_A : ∀ i : Fin n, i ∈ A → Share p) -- Fixed shares for A
    (S1 S2 : ZMod p) :
    Set.ncard {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S1 ρ i = shares_A i hi} =
    Set.ncard {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S2 ρ i = shares_A i hi} := by
  have h_bij := shift_is_bijection h_disjoint h_nonempty h_unauth shares_A (S1 := S1) (S2 := S2)
  rw [← h_bij.image_eq]
  rw [Set.InjOn.ncard_image h_bij.injOn]


/-
Helper lemma: The qualified set chosen by GenerateShares is the correct one due to disjointness.
-/
theorem GenerateShares_Q_eq {n : ℕ} {Qs : Set (Set (Fin n))}
    (h_disjoint : Qs.PairwiseDisjoint id)
    {Q : Set (Fin n)} (hQ : Q ∈ Qs)
    {i : Fin n} (hi : i ∈ Q) :
    Classical.choose (show ∃ Q' ∈ Qs, i ∈ Q' from ⟨Q, hQ, hi⟩) = Q := by
  let P := fun Q' => Q' ∈ Qs ∧ i ∈ Q'
  let Q' := Classical.choose (show ∃ Q' ∈ Qs, i ∈ Q' from ⟨Q, hQ, hi⟩)
  have hQ' : Q' ∈ Qs ∧ i ∈ Q' := Classical.choose_spec (show ∃ Q' ∈ Qs, i ∈ Q' from ⟨Q, hQ, hi⟩)
  have h_inter : i ∈ Q' ∩ Q := ⟨hQ'.2, hi⟩
  have h_not_disjoint : ¬Disjoint Q' Q := Set.not_disjoint_iff.mpr ⟨i, h_inter⟩
  by_contra h_ne
  have h_disj := h_disjoint hQ'.1 hQ h_ne
  contradiction

theorem GenerateShares_isValid {n : ℕ} {p : ℕ} [Fact p.Prime]
    (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (S : ZMod p) (ρ : Fin n → ZMod p) :
    IsValidSharing Qs S (GenerateShares Qs S ρ) := by

  refine ⟨?h1, ?h2, ?h3⟩
  /- 1) Participants not in any Q ∈ Qs get `none`. -/
  · intro i hi
    -- hi : (∀ Q ∈ Qs, i ∉ Q)
    have hneg : ¬ (∃ Q ∈ Qs, i ∈ Q) := by
      intro hex
      rcases hex with ⟨Q, hQ, hiQ⟩
      exact (hi Q hQ) hiQ
    -- Now unfold and take the `else` branch
    simp [GenerateShares, hneg]
  /- 2) Participants in a qualified set get `some _` (i.e. `.isSome`). -/
  · intro Q hQ i hiQ
    have hex : ∃ Q' ∈ Qs, i ∈ Q' := ⟨Q, hQ, hiQ⟩
    simp [GenerateShares, hex]
    split_ifs <;> simp
  /- 3) For each Q ∈ Qs, the sum over Q of shares equals S. -/
  · intro Q hQ
    -- Define the finite set Qfin.
    let Qfin : Finset (Fin n) := (Set.toFinite Q).toFinset

    -- Establish non-emptiness to pick a 'last' element.
    have hQ_nonempty : Q.Nonempty := h_nonempty Q hQ
    have hQfin_nonempty : Qfin.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact hQ_nonempty

    let last := Qfin.max' hQfin_nonempty
    have hlast_mem : last ∈ Qfin := Qfin.max'_mem hQfin_nonempty

    -- We define 'g' as the numeric value of the share.
    let g : Fin n → ZMod p := fun i => (GenerateShares Qs S ρ i).getD 0

    -- Goal: (∑ i : Fin n, if i ∈ Q then g i else 0) = S

    -- Step 1: Restrict the sum from 'Fin n' to 'Qfin'.
    -- The LHS is sum_{i \in Fin n} (if i \in Q then g i else 0).
    -- This is exactly sum_{i \in Qfin} g i, because Qfin contains exactly the i's where i \in Q.
    have h_sum_restrict : (∑ i : Fin n, if i ∈ Q then g i else 0) = ∑ i ∈ Qfin, g i := by
       rw [← Finset.sum_filter]

       -- We now need to show: ∑ i in univ.filter (· ∈ Q), g i = ∑ i in Qfin, g i
       apply Finset.sum_congr
       · -- Goal: univ.filter (· ∈ Q) = Qfin
         ext x
         simp only [Finset.mem_filter, Finset.mem_univ, true_and]
         -- Qfin is defined as (toFinite Q).toFinset
         -- So x ∈ Qfin ↔ x ∈ Q
         simp only [Qfin]
         simp only [Set.toFinite_toFinset, Set.mem_toFinset]
       · -- Goal: ∀ x ∈ univ.filter ..., g x = g x
         intros _ _
         rfl

    rw [h_sum_restrict]

    -- Step 2: Characterize 'g' inside Qfin.
    have hg_in_Q : ∀ i ∈ Qfin, g i = if i = last then S - ∑ j ∈ Qfin.erase last, ρ j else ρ i := by
      intro i hi
      dsimp [g]
      -- We are in Q.
      have hiQ : i ∈ Q := by
        have : i∈Q ↔ i ∈ Qfin := by
          have h1 : i ∈ Q ↔ Q i := by rfl
          simp only [Qfin]
          simp only [Set.toFinite_toFinset, Set.mem_toFinset]
        exact this.mpr hi

      -- Existence witness for GenerateShares
      have hex : ∃ Q' ∈ Qs, i ∈ Q' := ⟨Q, hQ, hiQ⟩

      -- Expand GenerateShares
      unfold GenerateShares
      rw [dif_pos hex]

      -- Crucial: The chosen Q' must be Q by disjointness
      have h_Q_eq : Classical.choose hex = Q :=
        GenerateShares_Q_eq h_disjoint hQ hiQ

      -- Substitute Q for the chosen set.
      -- This makes the internal 'Q_finset' and 'last' definitionally equal to our 'Qfin' and 'last'
      -- because they are defined by the same terms on the same set Q.
      simp only [h_Q_eq]
      split_ifs <;> rfl

    -- Step 3: Split the sum into `last` and the remaining elements.
    rw [← Finset.insert_erase hlast_mem]
    rw [Finset.sum_insert (by simp)]

    -- Evaluate the `last` term.
    rw [hg_in_Q last hlast_mem]
    rw [if_pos rfl]

    -- Evaluate the remaining terms.
    have h_sum_others :
        (∑ x ∈ Qfin.erase last, g x) = ∑ x ∈ Qfin.erase last, ρ x := by
      apply Finset.sum_congr rfl
      intro x hx

      have hx_in : x ∈ Qfin := Finset.mem_of_mem_erase hx
      have hx_ne : x ≠ last := Finset.ne_of_mem_erase hx

      rw [hg_in_Q x hx_in]
      rw [if_neg hx_ne]

    rw [h_sum_others]

    -- Step 4: Final algebra.
    ring



/-
Correctness of reconstruction: if G contains a qualified set, it recovers S.
-/
theorem ReconstructSecret_correct {n : ℕ} {p : ℕ} [Fact p.Prime]
    (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (S : ZMod p) (ρ : Fin n → ZMod p)
    (G : Set (Fin n))
    (hG : ∃ Q ∈ Qs, Q ⊆ G) :
    ReconstructSecret Qs (GenerateShares Qs S ρ) G = some S := by
  unfold ReconstructSecret;
  have := Classical.choose_spec hG;
  have h_sum_shares : ∑ i ∈ (Set.toFinite (Classical.choose hG)).toFinset, (GenerateShares Qs S ρ i).getD 0 = S := by
    have h_valid : IsValidSharing Qs S (GenerateShares Qs S ρ) := by
      exact GenerateShares_isValid Qs h_disjoint h_nonempty S ρ
    convert h_valid.2.2 _ this.1 using 1;
    rw [ ← Finset.sum_filter ] ; congr ; ext ; aesop;
  aesop


open AccessStructure SecretSharingScheme

-- We define the specific Access Structure for Disjoint Sets
def DisjointAS (Qs : Set (Set (Fin n))) : AccessStructure n where
  auth := {A | ∃ Q ∈ Qs, Q ⊆ A}
  h_monotone := by
    intro A B hA hsub
    obtain ⟨Q, hQ, hQA⟩ := hA
    use Q, hQ
    exact Set.Subset.trans hQA hsub


noncomputable def DisjointScheme {n : ℕ} (p : ℕ)
    [Fact p.Prime] (Qs : Set (Set (Fin n)))
    : SecretSharingScheme n := {
  Secret := ZMod p
  Random := Fin n → ZMod p
  Share := fun _ => Option (ZMod p)
  dealer := fun s ρ i => GenerateShares Qs s ρ i
  hSecret_card := by
    simpa using Nat.Prime.two_le Fact.out
  μ := PMF.uniformOfFintype (Fin n → ZMod p)
}

noncomputable def DisjointReconstruction {n : ℕ} (p : ℕ) [Fact p.Prime] (Qs : Set (Set (Fin n))) :
  ReconstructionAlgorithm (DisjointScheme p Qs) (DisjointAS Qs) :=
  fun B _hB shares =>
    let full_shares : Fin n → Option (ZMod p) := fun i =>
      if h : i ∈ B then shares ⟨i, h⟩ else none
    match ReconstructSecret Qs full_shares B with
    | some s => s
    | none   => (0 : ZMod p)

theorem DisjointScheme_Correctness {n : ℕ} (p : ℕ) [Fact p.Prime] (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty) :
    Correctness (DisjointScheme p Qs) (DisjointAS Qs) (DisjointReconstruction p Qs) := by
  intro s r B hB
  simp [DisjointReconstruction, shares_of_set, DisjointScheme]
  -- We need to show `full_shares` behaves like `GenerateShares` on `B`.
  -- And since `B` contains a qualified set, `ReconstructSecret` should work.
  have h_recon := ReconstructSecret_correct Qs h_disjoint h_nonempty s r B hB
  -- The `ReconstructSecret` in `DisjointReconstruction` uses `full_shares`.
  -- We need to show that `ReconstructSecret` with `full_shares` returns `some s`.
  convert congr_arg Option.get! h_recon using 1;
  unfold ReconstructSecret;
  split_ifs <;>
  simp
  · exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( by exact Classical.choose_spec ( ‹∃ Q ∈ Qs, Q ⊆ B› ) |>.2 ( by simpa using hx ) ) ] ;
  · rfl


/-
Perfect security theorem: The number of random tapes consistent with a given set of shares on an unauthorized set is independent of the secret.
-/
theorem PerfectSecurity_card_eq {n : ℕ} {p : ℕ} [Fact p.Prime]
    (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty)
    (A : Set (Fin n))
    (h_unauth : ∀ Q ∈ Qs, ¬(Q ⊆ A)) -- A is unauthorized
    (shares_A : ∀ i : Fin n, i ∈ A → Share p) -- Fixed shares for A
    (S1 S2 : ZMod p) :
    Set.ncard {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S1 ρ i = shares_A i hi} =
    Set.ncard {ρ | ∀ (i : Fin n) (hi : i ∈ A), GenerateShares Qs S2 ρ i = shares_A i hi} := by
  have h_bij := shift_is_bijection h_disjoint h_nonempty h_unauth shares_A (S1 := S1) (S2 := S2)
  rw [← h_bij.image_eq]
  rw [Set.InjOn.ncard_image h_bij.injOn]


theorem DisjointScheme_Security {n : ℕ} (p : ℕ) [Fact p.Prime] (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty) :
    PerfectSecurity (DisjointScheme p Qs) (DisjointAS Qs) := by
  unfold SecretSharingScheme.PerfectSecurity DisjointScheme DisjointAS;
  intro B hB s s';
  ext x;
  have h_card : Set.ncard {ρ : Fin n → ZMod p | shares_of_set (DisjointScheme p Qs) s ρ B = x} = Set.ncard {ρ : Fin n → ZMod p | shares_of_set (DisjointScheme p Qs) s' ρ B = x} := by
    have := PerfectSecurity_card_eq Qs h_disjoint h_nonempty B (by
    exact fun Q hQ hQB => hB ⟨ Q, hQ, hQB ⟩) (fun i hi => x ⟨i, hi⟩) s s';
    convert this using 1;
    · congr with ρ ; simp +decide [ funext_iff, shares_of_set ];
      rfl;
    · congr with ρ ; simp +decide [ funext_iff, shares_of_set ];
      rfl;
  simp_all [ Set.ncard_eq_toFinset_card', tsum_fintype ];
  simp_all [ eq_comm, Finset.sum_ite ];
  convert congr_arg ( · * ( p ^ n : ENNReal ) ⁻¹ ) ( congr_arg ( fun x : ℕ => ( x : ENNReal ) ) h_card )
  -- using 1

/--
  The function `DisjointReconstruction` realizes the disjoint access structure
-/
noncomputable def DisjointRealizedScheme {n : ℕ} (p : ℕ) [Fact p.Prime] (Qs : Set (Set (Fin n)))
    (h_disjoint : Qs.PairwiseDisjoint id)
    (h_nonempty : ∀ Q ∈ Qs, Q.Nonempty) :
    RealizedSecretSharingScheme n (DisjointAS Qs) := {
  toSecretSharingScheme := DisjointScheme p Qs
  recon := DisjointReconstruction p Qs
  h_correctness := DisjointScheme_Correctness p Qs h_disjoint h_nonempty
  h_security := DisjointScheme_Security p Qs h_disjoint h_nonempty
}

end DisjointAccessStructure
