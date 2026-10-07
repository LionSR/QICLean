/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaExcitationDecomposition
import QICLean.Representation.TensorPowerAction

/-!
# Permutation symmetry of exact excitation components

A physical copy permutation sends the exact sector indexed by `B` to the sector
indexed by its image. Consequently the projection onto this sector preserves
simultaneous physical and auxiliary symmetry for permutations stabilizing `B`.
The identity physical permutation also gives preservation of each auxiliary
label sector. These are the component symmetries used before the good-copy
estimates in the OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456.

The algebraic identities require no normalization of the one-copy vector and
include zero copies. When that vector is unit, the existing excitation-sector
theorem identifies these matrices as the actual orthogonal projections.
-/

/-
Original exact-excitation covariance and stabilizer symmetry supporting OpenAI,
A two-dimensional area law from a global spectral gap, September 24, 2026,
07-comparators.tex lines 441–456, comparator:defect-mass.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8750-qic-excitation-stabilizer-01
Matrix.permOp_mul_replicaExcitationProjection
Provenance-ID: 8750-qic-excitation-stabilizer-02
Matrix.commute_replicaExcitationProjection_kronecker_of_image_eq
Provenance-ID: 8750-qic-excitation-stabilizer-03
Matrix.replicaExcitationProjection_kronecker_mulVec_preserves_fixed
-/

open Matrix PermutationRepresentation TensorPower
open scoped Matrix Kronecker
namespace Matrix
variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem replicaExcitationProjection_image_apply (Ω : A → ℂ) (k : ℕ)
    (B : Finset (Fin k)) (σ : Equiv.Perm (Fin k)) (x y : Fin k → A) :
    replicaExcitationProjection Ω k (B.image σ)
      (copyPerm A k σ x) (copyPerm A k σ y) =
      replicaExcitationProjection Ω k B x y := by
  classical
  simp only [replicaExcitationProjection, finKronecker_apply, copyPerm_apply]
  refine Fintype.prod_equiv σ.symm _ _ fun j => ?_
  simp only [Equiv.Perm.inv_def]
  simp only [Finset.mem_image, ← Equiv.eq_symm_apply, exists_eq_right]

/-- A copy permutation carries the actual sector `B` to its image `σ B`.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456. -/
theorem permOp_mul_replicaExcitationProjection (Ω : A → ℂ) (k : ℕ)
    (B : Finset (Fin k)) (σ : Equiv.Perm (Fin k)) :
    permOp (copyPerm A k) σ * replicaExcitationProjection Ω k B =
      replicaExcitationProjection Ω k (B.image σ) * permOp (copyPerm A k) σ := by
  classical
  simp only [permOp_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  change replicaExcitationProjection Ω k B ((copyPerm A k σ)⁻¹ x) y =
    replicaExcitationProjection Ω k (B.image σ) x (copyPerm A k σ y)
  simpa only [Equiv.apply_symm_apply, Equiv.Perm.inv_def] using
    (replicaExcitationProjection_image_apply Ω k B σ ((copyPerm A k σ).symm x) y).symm
/-- The physical exact-sector projection commutes with a simultaneous physical
and auxiliary action whenever the physical permutation preserves the excited
subset. The auxiliary operator is arbitrary. OpenAI area-law manuscript,
`07-comparators.tex`, lines 441–456. -/
theorem commute_replicaExcitationProjection_kronecker_of_image_eq {C : Type*}
    [Fintype C] [DecidableEq C] (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k))
    (σ : Equiv.Perm (Fin k)) (hB : B.image σ = B) (M : Matrix C C ℂ) :
    Commute (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ))
      (permOp (copyPerm A k) σ ⊗ₖ M) := by
  have h := permOp_mul_replicaExcitationProjection Ω k B σ
  rw [hB] at h
  change (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *
      (permOp (copyPerm A k) σ ⊗ₖ M) =
    (permOp (copyPerm A k) σ ⊗ₖ M) *
      (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ))
  simp only [← mul_kronecker_mul, one_mul, mul_one, h]

/-- The exact excitation component inherits every simultaneous symmetry whose
physical copy permutation preserves its excited subset. For the identity
permutation and an auxiliary label projector, this also preserves the given
whole-copy auxiliary label. OpenAI area-law manuscript, `07-comparators.tex`,
lines 441–456. -/
theorem replicaExcitationProjection_kronecker_mulVec_preserves_fixed {C : Type*}
    [Fintype C] [DecidableEq C] (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k))
    (σ : Equiv.Perm (Fin k)) (hB : B.image σ = B) (M : Matrix C C ℂ)
    (v : (Fin k → A) × C → ℂ) (hv : (permOp (copyPerm A k) σ ⊗ₖ M) *ᵥ v = v) :
    (permOp (copyPerm A k) σ ⊗ₖ M) *ᵥ
        ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v) =
      (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v := by
  rw [mulVec_mulVec,
    ← (commute_replicaExcitationProjection_kronecker_of_image_eq Ω k B σ hB M).eq,
    ← mulVec_mulVec, hv]
end Matrix
