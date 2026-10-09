/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectCoordinateCovariance
import QICLean.Algebra.OrthogonalProjection

/-!
# One low-defect projection for every regional cut

The original physical vector and the two auxiliary labels define a single
projection on the original full configuration space. It is independent of
the regional partition. The five-factor projection for any disjoint cut,
formed from the same physical vector in the corresponding coordinates,
pulls back to this common projection exactly.

The common projection is contained in simultaneous symmetry. Thus the
same symmetric isometry gives one common compressed projection for every
cut; no per-leaf projection identity is assumed.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 20--37, 421--456 and 603--615, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section
open TensorPower PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance regionalLowDefectProjection_decidableEqGlobalPhysical :
    DecidableEq ((v : V) → β v) := Fintype.decidablePiFintype

local instance regionalLowDefectProjection_decidableEqGlobalConfig (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β C) R)) :=
  Fintype.decidablePiFintype

/-- The global physical/auxiliary coordinate equivalence carries joint
copy symmetry to symmetry of the original full configuration. Source:
`07-comparators.tex`, lines 80--110 and 421--456. -/
theorem symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv (k : ℕ) :
    (symProj (replicaJointCopyPerm ((v : V) → β v) C R k)).submatrix
      (globalReplicaCopiesEquiv β C R k) (globalReplicaCopiesEquiv β C R k) =
      symProj (copyPerm ((v : Option (Option V)) →
        addedSiteSpace (addedSiteSpace β C) R v) k) := by
  let e := globalReplicaCopiesEquiv β C R k
  have haction (σ : Equiv.Perm (Fin k))
      (x : Config k (addedSiteSpace (addedSiteSpace β C) R)) :
      replicaJointCopyPerm ((v : V) → β v) C R k σ (e x) =
        e (copyPerm ((v : Option (Option V)) →
          addedSiteSpace (addedSiteSpace β C) R v) k σ x) := rfl
  have h := congrArg (fun M => M.submatrix e e) (symProj_of_intertwine e haction)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id] using h

end TensorPower

namespace Matrix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance regionalLowDefectProjection_decidableEqPhysical :
    DecidableEq ((v : V) → β v) := Fintype.decidablePiFintype

local instance regionalLowDefectProjection_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β C) R)) :=
  Fintype.decidablePiFintype

/-- The common actual low-defect projection on the original site family.
Its definition contains no regional cut or metric. Source:
`07-comparators.tex`, lines 421--456. -/
def globalReplicaLowDefectProjection (Ω : ((v : V) → β v) → ℂ) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R))
      (Config k (addedSiteSpace (addedSiteSpace β C) R)) ℂ :=
  (replicaLowDefectProjection (C := C) (R := R) Ω k ellC ellR τ).submatrix
    (globalReplicaCopiesEquiv β C R k) (globalReplicaCopiesEquiv β C R k)

/-- The single global cutoff is a projection contained in simultaneous
symmetry, and its compression in any fixed symmetric coordinates is a
projection. Source: `07-comparators.tex`, lines 421--456 and 603--615. -/
theorem globalReplicaLowDefectProjection_properties
    (Ω : ((v : V) → β v) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    let P := globalReplicaLowDefectProjection β C R Ω k ellC ellR τ
    let Q := symProj (copyPerm ((v : Option (Option V)) →
      addedSiteSpace (addedSiteSpace β C) R v) k)
    IsStarProjection P ∧ P * Q = P ∧
      ∀ (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R)) (Fin n) ℂ),
        Z * Zᴴ = Q → IsStarProjection (Zᴴ * P * Z) := by
  intro P Q
  let e := globalReplicaCopiesEquiv β C R k
  let P₀ := replicaLowDefectProjection (C := C) (R := R) Ω k ellC ellR τ
  let Q₀ := symProj (replicaJointCopyPerm ((v : V) → β v) C R k)
  have hP₀ : IsStarProjection P₀ := isStarProjection_replicaLowDefectProjection
    Ω hΩ k ellC ellR τ
  have hP : IsStarProjection P := by
    refine ⟨?_, (hP₀.isSelfAdjoint.isHermitian.submatrix e).isSelfAdjoint⟩
    change P₀.submatrix e e * P₀.submatrix e e = P₀.submatrix e e
    rw [Matrix.submatrix_mul_equiv, hP₀.isIdempotentElem.eq]
  have hP₀Q₀ : P₀ * Q₀ = P₀ := by
    change (_ * _ * Q₀) * Q₀ = _ * _ * Q₀
    rw [Matrix.mul_assoc, ((exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
      (X := (Fin k → ((v : V) → β v)) × ((Fin k → C) × (Fin k → R)))).elim
        (fun l hl => Eq.mp (congrArg IsStarProjection
          (hl (replicaJointCopyPerm ((v : V) → β v) C R k)))
            (show IsStarProjection
              (labelProj (replicaJointCopyPerm ((v : V) → β v) C R k) l) from
                ⟨labelProj_mul_self _ l, (isHermitian_labelProj _ l).isSelfAdjoint⟩))).isIdempotentElem.eq]
  have hPQ : P * Q = P := by
    dsimp only [Q]
    rw [← symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv β C R k]
    change P₀.submatrix e e * Q₀.submatrix e e = P₀.submatrix e e
    rw [Matrix.submatrix_mul_equiv, hP₀Q₀]
  refine ⟨hP, hPQ, ?_⟩
  intro n Z hZZ
  exact isStarProjection_conjTranspose_mul_mul_of_mul_range_eq hP Z
    (by simpa only [hZZ] using hPQ)

/-- Every actual five-factor low-defect projection pulls back to the same
global projection. The physical vector is the original vector transported
by the explicit regional equivalence; the two auxiliary labels are
unchanged. Source: `07-comparators.tex`, lines 20--37 and 421--456. -/
theorem regionalFiveFactor_lowDefectProjection_eq_global
    (Ω : ((v : V) → β v) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (Q Y : Finset V) (hQY : Disjoint Q Y) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    let ι := regionalFiveFactorSpace β C R Q Y
    let e := regionalFiveFactorCopyEquiv β C R Q Y hQY k
    let Ωcut := Ω ∘ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY).symm
    let Pcut := (replicaLowDefectProjection (C := C) (R := R)
      Ωcut k ellC ellR τ).submatrix (fiveFactorCopiesEquiv ι k) (fiveFactorCopiesEquiv ι k)
    Pcut.submatrix e e = globalReplicaLowDefectProjection β C R Ω k ellC ellR τ := by
  intro ι e Ωcut Pcut
  have h := replicaLowDefectProjection_reindex_physical (C := C) (R := R)
    Ω hΩ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY) k ellC ellR τ
  change ((replicaLowDefectProjection (C := C) (R := R)
    Ωcut k ellC ellR τ).submatrix (fiveFactorCopiesEquiv ι k)
      (fiveFactorCopiesEquiv ι k)).submatrix e e = _
  rw [h]
  ext x y
  simp only [Matrix.submatrix_apply, globalReplicaLowDefectProjection, e, ι,
    regionalFiveFactorCopyEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

end Matrix
