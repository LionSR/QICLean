/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.AddedSiteTensorInsertion

/-!
# Symmetry under a literal added-site insertion

Inserting the same arbitrary vector at an additional site in every copy
intertwines simultaneous copy permutations. Averaging gives the corresponding
identity for the existing symmetric-space projections. Hence a symmetric
vector remains symmetric after insertion. No norm hypothesis on the inserted
vector is required, and zero copies and empty coordinate sets are allowed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, lines 14–27, and
  `07-comparators.tex`, lines 283–308, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v

noncomputable section

open Matrix PermutationRepresentation

namespace TensorPower

variable {F : Type v} [Fintype F] [DecidableEq F]
variable (ι : F → Type u) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (A : Type u) [Fintype A] [DecidableEq A]

/-- The actual insertion intertwines the simultaneous permutation of all
copies. This is the all-site specialization of the subsystem identity.
Source: area-law manuscript, `05-replicas.tex`, lines 14–27, and
`07-comparators.tex`, lines 283–308. -/
theorem permOp_copyPerm_mul_addedSiteInsertion (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (b : A → ℂ) :
    permOp (copyPerm ((o : Option F) → addedSiteSpace ι A o) k) σ *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * permOp (copyPerm ((f : F) → ι f) k) σ := by
  classical
  have hfull : insert none ((Finset.univ : Finset F).image some) =
      (Finset.univ : Finset (Option F)) := by
    ext o
    cases o <;> simp
  simpa only [hfull, subsystemPerm_univ] using
    permOp_mul_addedSiteInsertion ι A k Finset.univ σ b

/-- Averaging the actual simultaneous-copy identity gives the exact
intertwining of the existing symmetry projections.
Source: area-law manuscript, `05-replicas.tex`, lines 14–27, and
`07-comparators.tex`, lines 283–308. -/
theorem symProj_mul_addedSiteInsertion (k : ℕ) (b : A → ℂ) :
    symProj (copyPerm ((o : Option F) → addedSiteSpace ι A o) k) *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * symProj (copyPerm ((f : F) → ι f) k) := by
  classical
  simp only [symProj, Matrix.smul_mul, Matrix.mul_smul, Matrix.sum_mul,
    Matrix.mul_sum, permOp_copyPerm_mul_addedSiteInsertion]

/-- A symmetric vector remains symmetric under the literal insertion of
the same vector in every copy. No normalization of either vector is needed.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem addedSiteInsertion_mulVec_mem_symmetricSubspace (k : ℕ) (b : A → ℂ)
    {v : Config k ι → ℂ} (hv : v ∈ symmetricSubspace k ι) :
    addedSiteInsertion ι A k b *ᵥ v ∈ symmetricSubspace k (addedSiteSpace ι A) := by
  change ∀ σ, permOp (copyPerm ((o : Option F) → addedSiteSpace ι A o) k) σ *ᵥ
    (addedSiteInsertion ι A k b *ᵥ v) = addedSiteInsertion ι A k b *ᵥ v
  intro σ
  rw [Matrix.mulVec_mulVec, permOp_copyPerm_mul_addedSiteInsertion,
    ← Matrix.mulVec_mulVec, hv σ]

end TensorPower
