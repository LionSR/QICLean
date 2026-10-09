/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectProjection
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Algebra.OrthogonalProjection
import QICLean.Representation.SymmetricProjectionCoordinates

/-!
# The actual low-defect projection in symmetric coordinates

The five-factor coordinate equivalence identifies simultaneous permutation
of all five site factors with simultaneous permutation of the whole
physical copy and the two auxiliary copies. Consequently the actual
low-defect projection, including its two original auxiliary labels,
is contained in the full symmetric space. Its compression in any fixed
coordinates for that space is again an orthogonal projection.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421--456 and 603--615, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace TensorPower

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance replicaLowDefectSymmetricCoordinates_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- Literal five-factor coordinates identify the joint physical/auxiliary
symmetry projection with the full configuration symmetry projection.
Source: `07-comparators.tex`, lines 421--456. -/
theorem symProj_replicaJointCopyPerm_submatrix_fiveFactorCopiesEquiv (k : ℕ) :
    (symProj (replicaJointCopyPerm (ι 0 × (ι 1 × ι 2)) (ι 3) (ι 4) k)).submatrix
      (fiveFactorCopiesEquiv ι k) (fiveFactorCopiesEquiv ι k) =
      symProj (copyPerm ((f : Fin 5) → ι f) k) := by
  let e := fiveFactorCopiesEquiv ι k
  have haction (σ : Equiv.Perm (Fin k)) (x : Config k ι) :
      replicaJointCopyPerm (ι 0 × (ι 1 × ι 2)) (ι 3) (ι 4) k σ (e x) =
        e (copyPerm ((f : Fin 5) → ι f) k σ x) := rfl
  simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id] using
    congrArg (fun M => M.submatrix e e) (symProj_of_intertwine e haction)

/-- The actual low-defect sector is an orthogonal projection after
compression by the same fixed symmetric coordinates. The original
physical vector is only assumed to have norm one, and no metric occurs
in this statement. Source: `07-comparators.tex`, lines 421--456 and 603--615. -/
theorem isStarProjection_compressed_replicaLowDefectProjection
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ)
    {n : ℕ} (Z : Matrix (Config k ι) (Fin n) ℂ)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((f : Fin 5) → ι f) k)) :
    let P := Matrix.replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
    let e := fiveFactorCopiesEquiv ι k
    IsStarProjection (Zᴴ * P.submatrix e e * Z) := by
  intro P e
  let S := symProj (replicaJointCopyPerm (ι 0 × (ι 1 × ι 2)) (ι 3) (ι 4) k)
  have hP : IsStarProjection P := Matrix.isStarProjection_replicaLowDefectProjection
    Ω hΩ k ellC ellR τ
  have hPS : P * S = P := by
    change (_ * _ * S) * S = _ * _ * S
    obtain ⟨l, hl⟩ := exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
      (X := (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)))
    rw [Matrix.mul_assoc, ← hl (replicaJointCopyPerm (ι 0 × (ι 1 × ι 2))
      (ι 3) (ι 4) k), labelProj_mul_self]
  have hPe : IsStarProjection (P.submatrix e e) := by
    refine ⟨?_, (hP.isSelfAdjoint.isHermitian.submatrix e).isSelfAdjoint⟩
    change P.submatrix e e * P.submatrix e e = P.submatrix e e
    rw [Matrix.submatrix_mul_equiv, hP.isIdempotentElem.eq]
  apply Matrix.isStarProjection_conjTranspose_mul_mul_of_mul_range_eq hPe Z
  rw [hZZ, ← symProj_replicaJointCopyPerm_submatrix_fiveFactorCopiesEquiv ι k]
  change P.submatrix e e * S.submatrix e e = P.submatrix e e
  rw [Matrix.submatrix_mul_equiv, hPS]

end TensorPower
