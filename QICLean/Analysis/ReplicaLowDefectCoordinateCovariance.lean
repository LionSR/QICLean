/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectProjection
import QICLean.Analysis.CfcConjugation
import QICLean.Representation.RegionalFiveFactorCoordinates
import QICLean.Representation.SymmetricProjectionCoordinates

/-!
# Physical coordinate covariance of the actual low-defect projection

Changing the coordinates of the original physical vector transports its
rank-one projector, its replica defect count, and its spectral cutoff.
The two auxiliary copy registers and their original representation labels
are unchanged. Simultaneous copy symmetry is transported by the same
literal equivalence. Thus the resulting low-defect projection is the
coordinate transform of a single original projection.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421--456 and 603--615, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- One-copy coordinate changes commute with the literal sum of replica
Hamiltonians. Source: `07-comparators.tex`, `comparator:defect-mass`, lines 421--438. -/
theorem replicaHamiltonian_submatrix_equiv (H : Matrix A A ℂ) (e : A ≃ B) (k : ℕ) :
    replicaHamiltonian (H.submatrix e.symm e.symm) k =
      (replicaHamiltonian H k).submatrix
        (Equiv.arrowCongr (Equiv.refl (Fin k)) e).symm
        (Equiv.arrowCongr (Equiv.refl (Fin k)) e).symm := by
  ext x y
  simp only [replicaHamiltonian, Matrix.submatrix_apply, Matrix.sum_apply, finKronecker_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · simp only [hji, ite_true, Matrix.submatrix_apply]
  · simp only [hji, ite_false, Matrix.one_apply]
    change (if x j = y j then (1 : ℂ) else 0) =
      if e.symm (x j) = e.symm (y j) then 1 else 0
    simp only [e.symm.injective.eq_iff]

/-- The original rank-one ground projector, and hence the full defect
count, transforms under a physical coordinate equivalence. The vector
need not be normalized for this identity. Source: `07-comparators.tex`,
`comparator:defect-mass`, lines 421--438. -/
theorem replicaDefectCount_submatrix_equiv (Ω : A → ℂ) (e : A ≃ B) (k : ℕ) :
    replicaDefectCount (Ω ∘ e.symm) k =
      (replicaDefectCount Ω k).submatrix
        (Equiv.arrowCongr (Equiv.refl (Fin k)) e).symm
        (Equiv.arrowCongr (Equiv.refl (Fin k)) e).symm := by
  have hground : 1 - vecMulVec (Ω ∘ e.symm) (star (Ω ∘ e.symm)) =
      (1 - vecMulVec Ω (star Ω)).submatrix e.symm e.symm := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
      vecMulVec_apply, Pi.star_apply, Function.comp_apply, e.symm.injective.eq_iff]
  change replicaHamiltonian (1 - vecMulVec (Ω ∘ e.symm) (star (Ω ∘ e.symm))) k = _
  rw [hground]
  exact replicaHamiltonian_submatrix_equiv _ e k

end Matrix

namespace TensorPower

variable {A B C R : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

/-- Physical coordinate changes transport the full joint symmetry and
leave the original two auxiliary copy actions unchanged. Source:
`07-comparators.tex`, lines 421--456. -/
theorem symProj_replicaJointCopyPerm_reindex_physical (e : A ≃ B) (k : ℕ) :
    symProj (replicaJointCopyPerm B C R k) =
      (symProj (replicaJointCopyPerm A C R k)).submatrix
        (replicaPhysicalCoordinateEquiv (C := C) (R := R) e k).symm
        (replicaPhysicalCoordinateEquiv (C := C) (R := R) e k).symm := by
  let E := replicaPhysicalCoordinateEquiv (C := C) (R := R) e k
  have haction (σ : Equiv.Perm (Fin k))
      (x : (Fin k → A) × ((Fin k → C) × (Fin k → R))) :
      replicaJointCopyPerm B C R k σ (E x) = E (replicaJointCopyPerm A C R k σ x) := rfl
  exact symProj_of_intertwine E haction

end TensorPower

namespace Matrix

variable {A B C R : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

/-- The actual low-defect projection is covariant under a physical
coordinate equivalence, including its original two auxiliary labels and
simultaneous symmetry. No desired projection equality is assumed.
Source: `07-comparators.tex`, lines 421--456 and 603--615. -/
theorem replicaLowDefectProjection_reindex_physical
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (e : A ≃ B) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    replicaLowDefectProjection (C := C) (R := R) (Ω ∘ e.symm) k ellC ellR τ =
      (replicaLowDefectProjection (C := C) (R := R) Ω k ellC ellR τ).submatrix
        (replicaPhysicalCoordinateEquiv (C := C) (R := R) e k).symm
        (replicaPhysicalCoordinateEquiv (C := C) (R := R) e k).symm := by
  let eₖ := Equiv.arrowCongr (Equiv.refl (Fin k)) e
  let E := replicaPhysicalCoordinateEquiv (C := C) (R := R) e k
  let f : ℝ → ℝ := fun x => if x ≤ τ * k then 1 else 0
  let L := labelProj (copyPerm C k) ellC ⊗ₖ labelProj (copyPerm R k) ellR
  have hcut : cfc f (replicaDefectCount (Ω ∘ e.symm) k) ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ) =
      (cfc f (replicaDefectCount Ω k) ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)).submatrix
        E.symm E.symm := by
    rw [replicaDefectCount_submatrix_equiv Ω e k,
      cfc_submatrix_equiv (posSemidef_replicaDefectCount Ω hΩ k).isHermitian f eₖ]
    rfl
  have hlabels : (1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ L =
      ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ L).submatrix E.symm E.symm := by
    change (1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ L =
      ((1 : Matrix (Fin k → A) (Fin k → A) ℂ).submatrix eₖ.symm eₖ.symm) ⊗ₖ L
    rw [Matrix.submatrix_one_equiv]
  change (cfc f (replicaDefectCount (Ω ∘ e.symm) k) ⊗ₖ 1) *
      ((1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ L) *
      symProj (replicaJointCopyPerm B C R k) = _
  rw [hcut, hlabels, symProj_replicaJointCopyPerm_reindex_physical e k,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

end Matrix
