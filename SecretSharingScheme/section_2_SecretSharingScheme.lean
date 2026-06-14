import Mathlib.Tactic

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform

-- import the data structure defined in AccessStructure.lean
import SecretSharingScheme.section_1_AccessStructure


section SecretSharingScheme

/-
Data structure for Secret Sharing Scheme
-/
universe u v

/-
  A secret sharing scheme with `n` participants consist of the following data.

  `Secret` is a finite type and has size at least 2
  `Random` is another finite type that is nonempty
  The share of participant `i` has type `Share i`, for i = 0,1,..., n-1.
  We assume that `Share i` is a finite type for all `i`.
  share is a function that maps `Fin n` to `Type u`, representing the share of
  the `n` participants
  A `dealer` is a function that maps a pair of `Secret` and `Random` to the `n` shares.
-/
structure SecretSharingScheme (n : ℕ) where
  Secret : Type u
  Random : Type v
  [hSecret : Fintype Secret]
  hSecret_card : Fintype.card Secret ≥ 2
  Share : Fin n → Type u
  [hShare : ∀ i, Fintype (Share i)]
  [hRandom : Fintype Random]
  [hRandomNonempty : Nonempty Random]
  μ : PMF Random := PMF.uniformOfFintype Random
  dealer : Secret → Random → (∀ i, Share i)


namespace SecretSharingScheme

open AccessStructure

/-
Given a share s and a random string r, the restriction of Π(s,r) to A
is denoted `shares_of_set`. We may also denote it by Π_A(s,r)

`shares_of_set` is a function that maps s, r, and A to
a function from A to the shares associated with the participants in A
-/
def shares_of_set {n : ℕ} (scheme : SecretSharingScheme n)
  (s : scheme.Secret) (r : scheme.Random) (A : Set (Fin n)) : (i : A) → scheme.Share i :=
  fun i => scheme.dealer s r i

/-! Reconstruction algorithm
For every authorized subset `B`, the reconstruction algorithm is a function that
takes the shares in `B` as input and return a term of type `Secret`
-/
def ReconstructionAlgorithm {n : ℕ} (scheme : SecretSharingScheme n) (Γ : AccessStructure n) :=
  ∀ (B : Set (Fin n)), B ∈ Γ.auth → ((i : B) → scheme.Share i) → scheme.Secret

/-
Correctness means that for every authorized set B ∈ Γ, and secret s ∈ S, the participants in B can reconstruct the secret correctly with probability 1.
-/
def Correctness {n : ℕ} (S : SecretSharingScheme n) (Γ : AccessStructure n) (recon : ReconstructionAlgorithm S Γ) :=
  ∀ (s : S.Secret) (r : S.Random) (B : Set (Fin n)) (hB : B ∈ Γ.auth),
  recon B hB (shares_of_set S s r B) = s

/-
For every unauthorized set B ∉ Γ, the shares held by B reveal
no information about the secret.

Fix an unauthorized set B. For each secret s, (shares_of_set S s r B ) with r random
gives a distribution on |B|-tuple of shares. Perfect security requires that
this distribution is the same for all secret s. The equation in the condition is
$$
\Pr(\Pi_T(s_1,r) = \langle s_j\rangle_{j\in T}) =
\Pr(\Pi_T(s_2,r) = \langle s_j\rangle_{j\in T} )
$$
-/
def PerfectSecurity {n : ℕ} (S : SecretSharingScheme n) (Γ : AccessStructure n) :=
  ∀ (B : Set (Fin n)) (_hB : B ∉ Γ.auth) (s s' : S.Secret),
    (S.μ.map (fun r => shares_of_set S s r B )) =
    (S.μ.map (fun r => shares_of_set S s' r B))

/-
A structure representing a secret sharing scheme that realizes a given access structure Γ.
-/
structure RealizedSecretSharingScheme (n : ℕ) (Γ : AccessStructure n) extends SecretSharingScheme n where
  /-- The reconstruction algorithm for the scheme. -/
  recon : ReconstructionAlgorithm toSecretSharingScheme Γ
  /-- Proof of correctness: authorized sets can reconstruct the secret. -/
  h_correctness : Correctness toSecretSharingScheme Γ recon
  /-- Proof of perfect security: unauthorized sets learn nothing about the secret. -/
  h_security : PerfectSecurity toSecretSharingScheme Γ


/-
The size of secret is log(|S|).
-/
noncomputable def secret_size {n : ℕ} (scheme : SecretSharingScheme n) : ℝ :=
  letI _ := scheme.hSecret
  Real.log (Fintype.card scheme.Secret)

/-
The size of the share of participant i is log(|Si|).
-/
noncomputable def share_size {n : ℕ} (scheme : SecretSharingScheme n) (i : Fin n) : ℝ :=
  letI _ := scheme.hShare i
  Real.log (Fintype.card (scheme.Share i))

/-
The maximum share size is max_j log(|Sj|).
-/
noncomputable def max_share_size {n : ℕ} (scheme : SecretSharingScheme n) : ℝ :=
  letI _ := scheme.hShare
  (Finset.univ.image (fun i => share_size scheme i)).max.getD 0

/-
The Total share size is sum_j log(|Sj|).
-/
noncomputable def total_share_size {n : ℕ} (scheme : SecretSharingScheme n) : ℝ :=
  letI := scheme.hShare
  Finset.sum Finset.univ (fun i => share_size scheme i)

/-
The information ratio is max_j log(|Sj|) / log(|S|).
-/
noncomputable def information_ratio {n : ℕ} (scheme : SecretSharingScheme n) : ℝ :=
  (max_share_size scheme) / (secret_size scheme)


/-
To verify perfect security, we only need to verify the condition for maximally unauthorized set.
-/
theorem PerfectSecurity_iff_maximal {n : ℕ} (scheme : SecretSharingScheme n) (Γ : AccessStructure n) :
    PerfectSecurity scheme Γ ↔
    ∀ (T : Set (Fin n)), isMaximallyUnauthorized Γ T →
      ∀ (s1 s2 : scheme.Secret),
        (scheme.μ.map (fun r => shares_of_set scheme s1 r T)) =
        (scheme.μ.map (fun r => shares_of_set scheme s2 r T)) := by
          refine' ⟨ _, fun h => _ ⟩;
          · exact fun h T hT s1 s2 => h T hT.1 s1 s2
          · -- For any unauthorized set T, there exists a maximally unauthorized set T'
            -- such that T is a subset of T'.
            have h_max_unauthorized : ∀ T : Set (Fin n), T ∉ Γ.auth → ∃ T' : Set (Fin n),
                isMaximallyUnauthorized Γ T' ∧ T ⊆ T' := by
              intro T hT;
              -- Since $T$ is unauthorized, there exists a maximally
              -- unauthorized set $T'$ containing $T$.
              obtain ⟨T', hT'⟩ : ∃ T' : Set (Fin n), T ⊆ T' ∧ T' ∉ Γ.auth
                   ∧ ∀ B : Set (Fin n), T' ⊂ B → B ∈ Γ.auth := by
                have h_max : ∃ T' : Set (Fin n), T ⊆ T' ∧ T' ∉ Γ.auth
                   ∧ ∀ B : Set (Fin n), T' ⊂ B → B ∈ Γ.auth := by
                  have h_finite : Set.Finite {B : Set (Fin n) | T ⊆ B ∧ B ∉ Γ.auth} := by
                    exact Set.toFinite _
                  obtain ⟨T', hT'_max⟩ : ∃ T' ∈ {B : Set (Fin n) | T ⊆ B
                      ∧ B ∉ Γ.auth}, ∀ B ∈ {B : Set (Fin n) | T ⊆ B ∧ B ∉ Γ.auth}, T'.ncard ≥ B.ncard := by
                    apply_rules [ Set.exists_max_image ]
                    exact ⟨ T, Set.Subset.refl _, hT ⟩
                  exact ⟨ T', hT'_max.1.1, hT'_max.1.2, fun B hB => Classical.not_not.1 fun hB' => not_lt_of_ge
                    ( hT'_max.2 B ⟨ hT'_max.1.1.trans hB.1, hB' ⟩ ) ( Set.ncard_lt_ncard hB ) ⟩
                exact h_max
              exact ⟨ T', ⟨ hT'.2.1, hT'.2.2 ⟩, hT'.1 ⟩
            -- By combining the results from h_max_unauthorized and h, we can conclude the proof.
            intros T hT s1 s2
            obtain ⟨T', hT', hT'_superset⟩ := h_max_unauthorized T hT
            have h_eq : (scheme.μ.map (fun r => shares_of_set scheme s1 r T'))
               = (scheme.μ.map (fun r => shares_of_set scheme s2 r T')) := by
              exact h T' hT' s1 s2
            convert congr_arg ( fun f => f.map ( fun x => fun i : T => x ⟨ i, hT'_superset i.2 ⟩ ) )
                h_eq using 1 <;>
              simp [ PMF.map ];
            · congr! 2
            · congr! 2

end SecretSharingScheme -- namespace

end SecretSharingScheme  -- section
