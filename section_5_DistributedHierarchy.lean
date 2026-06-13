import Mathlib.Tactic

-- import AccessStructure and SecretSharingScheme
import SecretSharingScheme.section_1_AccessStructure
import SecretSharingScheme.section_2_SecretSharingScheme




section DistributedHierarchy

open AccessStructure SecretSharingScheme

/-!
### Abstract Distributed Matrix Multiplication Protocol
This structure defines the interface and correctness condition for any
distributed matrix multiplication scheme, independent of how it is implemented.
-/
structure DistributedMatrixMultiplication (n : ℕ) (Γ : AccessStructure n) (F : Type*) [Field F] where
  -- Types
  Secret : Type*
  Share : Fin n → Type*
  Random : Type* -- We need Randomness for LSSS compatibility

  -- Protocol Functions
  encode : Secret → Random → (i : Fin n) → Share i
  worker_compute : {d : ℕ} → (i : Fin n) → (Fin d → Share i) → (Fin d → F) → Share i
  reconstruct : (B : Set (Fin n)) → (hB : B ∈ Γ.auth) → ((i : B) → Share i) → Secret

  -- Algebraic Structure needed
  [secret_add : AddCommMonoid Secret]
  [secret_module : Module F Secret]

  -- correctness
    h_distributed_correctness :
    ∀ {d : ℕ} (A : Fin d → Secret) (K : Fin d → Random) (x : Fin d → F)
      (B : Set (Fin n)) (hB : B ∈ Γ.auth),
    let shares (j : Fin d) (i : Fin n) := encode (A j) (K j) i
    let responses (i : B) := worker_compute i (fun j => shares j i) x
    reconstruct B hB responses = ∑ j, x j • A j






/-!
### The Linear Secret Sharing Scheme (LSSS)
-/
structure LinearSecretSharingScheme (n : ℕ) (Γ : AccessStructure n) (F : Type*) [Field F]
    extends RealizedSecretSharingScheme n Γ where

  -- Algebraic Structures
  [secret_add : AddCommMonoid Secret]
  [random_add : AddCommMonoid Random]
  [share_add : ∀ i, AddCommMonoid (Share i)]

  [secret_module : Module F Secret]
  [random_module : Module F Random]
  [share_module : ∀ i, Module F (Share i)]

  -- Linearity of Dealer
  dealer_linear : (Secret × Random) →ₗ[F] (Π i, Share i)
  h_dealer_eq : ∀ s r, dealer_linear (s, r) = dealer s r

  -- Linearity of Reconstruction
  recon_linear : ∀ (B : Set (Fin n)) (_hB : B ∈ Γ.auth),
    ((i : B) → Share i) →ₗ[F] Secret
  h_recon_eq : ∀ (B : Set (Fin n)) (hB : B ∈ Γ.auth) (shares : (i : B) → Share i),
    recon_linear B hB shares = recon B hB shares




namespace LinearSecretSharingScheme

  -- Register instances
attribute [instance] secret_add random_add share_add
attribute [instance] secret_module random_module share_module

variable {n : ℕ} {Γ : AccessStructure n} {F : Type*} [Field F]
variable (L : LinearSecretSharingScheme n Γ F)

-- Definition of the Worker's Computation
def worker_compute_impl {d : ℕ} (i : Fin n) (shares : Fin d → L.Share i) (x : Fin d → F) : L.Share i :=
  ∑ j, x j • shares j

-- Definition of Target and Keys (Helpers for the proof)
def target_computation {d : ℕ} (A : Fin d → L.Secret) (x : Fin d → F) : L.Secret :=
  ∑ j, x j • A j

def aggregate_key {d : ℕ} (K : Fin d → L.Random) (x : Fin d → F) : L.Random :=
  ∑ j, x j • K j

-- lemma used in the Homomorphism Lemma
lemma sum_prod_smul
    {n : ℕ} {Γ : AccessStructure n} {F : Type*} [Field F]
    (L : LinearSecretSharingScheme n Γ F)
    {d : ℕ}
    (x : Fin d → F)
    (A : Fin d → L.Secret)
    (K : Fin d → L.Random) :
    ∑ j, x j • (A j, K j) = (∑ j, x j • A j, ∑ j, x j • K j) := by
  ext
  · simp only [Prod.fst_sum, Prod.smul_mk]
  · simp only [Prod.snd_sum, Prod.smul_mk]


-- The Homomorphism Lemma
lemma worker_homomorphism
    {d : ℕ} (A : Fin d → L.Secret) (K : Fin d → L.Random) (x : Fin d → F) (i : Fin n) :
    L.worker_compute_impl i (fun j => L.dealer (A j) (K j) i) x =
    L.dealer (target_computation L A x) (aggregate_key L K x) i := by

  let Ψ := L.dealer_linear
  calc worker_compute_impl L i (fun j => L.dealer (A j) (K j) i) x
    -- 1. Definition of worker_compute
    = ∑ j, x j • L.dealer (A j) (K j) i := rfl

    -- 2. Convert L.dealer to Ψ (the LinearMap) inside the sum
    _ = ∑ j, x j • (Ψ (A j, K j) i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← h_dealer_eq] -- Use the consistency property

    -- 3. Pull the evaluation 'i' outside the scalar multiplication
    -- (c • f) i = c • (f i)
    _ = ∑ j, (x j • Ψ (A j, K j)) i := rfl

    -- 4. Pull the evaluation 'i' outside the sum
    -- (∑ f) i = ∑ (f i)
    _ = (∑ j, x j • Ψ (A j, K j)) i := by
      rw [Finset.sum_apply]

    -- 5. Use Linearity of Ψ: ∑ c • Ψ(v) = Ψ(∑ c • v)
    _ = (Ψ (∑ j, x j • (A j, K j))) i := by
      rw [map_sum]
      -- Move scalar multiplication inside the map
      simp_rw [map_smul]

    -- 6. Combine the arguments inside the pair
    -- ∑ (x • A, x • K) = (∑ x A, ∑ x K)
    _ = (Ψ (∑ j, x j • A j, ∑ j, x j • K j)) i := by
      rw [sum_prod_smul]

    -- 7. Convert back to definitions of target_computation and aggregate_key
    _ = Ψ (target_computation L A x, aggregate_key L K x) i := rfl

    -- 8. Convert back to L.dealer
    _ = L.dealer (target_computation L A x) (aggregate_key L K x) i := by
      rw [h_dealer_eq]

-- The Main Theorem (Correctness)
theorem distributed_computing_correctness
    {d : ℕ} (A : Fin d → L.Secret) (K : Fin d → L.Random) (x : Fin d → F)
    (B : Set (Fin n)) (hB : B ∈ Γ.auth) :
    let worker_responses (i : B) := L.worker_compute_impl i (fun j => L.dealer (A j) (K j) i) x
    L.recon B hB worker_responses = target_computation L A x := by

  have h_valid_shares : (fun i : B => L.worker_compute_impl i (fun j => L.dealer (A j) (K j) i) x) =
      shares_of_set L.toSecretSharingScheme (target_computation L A x) (aggregate_key L K x) B := by
    ext i
    apply worker_homomorphism

  rw [h_valid_shares]
  exact L.h_correctness (target_computation L A x) (aggregate_key L K x) B hB


structure SecureDistributedMatrixMultiplication (n : ℕ) (Γ : AccessStructure n) (F : Type*) [Field F]
    extends LinearSecretSharingScheme n Γ F where
  /-
  Construct the DistributedMatrixMultiplication instance using the
  definitions and theorems from the LinearSecretSharingScheme namespace.
  -/
  toDistMatrixMul : DistributedMatrixMultiplication n Γ F := {
    Secret := Secret
    Share := Share
    Random := Random

    -- Map LSSS functions to Protocol functions
    encode := dealer
    reconstruct := recon
    worker_compute := fun i shares x => worker_compute_impl toLinearSecretSharingScheme i shares x

    -- Instances
    secret_add := secret_add
    secret_module := secret_module

    -- Proof of correctness
    h_distributed_correctness := by
      intros d A K x B hB
      apply distributed_computing_correctness toLinearSecretSharingScheme
  }

end LinearSecretSharingScheme


end DistributedHierarchy
