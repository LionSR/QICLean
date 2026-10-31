/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PosSemidefSupport
import QICLean.Algebra.MatrixAux
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Order comparison with the spectral support projection

A positive contraction lies below its range projection. This comparison is
used in the range-projection reduction of ALVV, arXiv:1602.08828v2,
Section 6.1, lines 1457–1460.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The existing spectral support projection is the indicator of the nonzero
spectrum applied to the same Hermitian matrix. ALVV, arXiv:1602.08828v2,
Section 6.1, lines 1457–1460. -/
theorem IsHermitian.supportProj_eq_cfc (hA : A.IsHermitian) :
    hA.supportProj = cfc (fun x : ℝ ↦ if x ≠ 0 then 1 else 0) A := by
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.supportProj Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : hA.eigenvalues i = 0 <;> simp [hi]
  · simp [Matrix.diagonal_apply_ne _ hij]

/-- The spectral support projection is a star projection on any finite index
space. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
theorem IsHermitian.isStarProjection_supportProj (hA : A.IsHermitian) :
    IsStarProjection hA.supportProj := by
  rw [isStarProjection_iff']
  exact ⟨hA.supportProj_idem, hA.supportProj_isHermitian⟩

/-- A positive contraction is dominated by its actual range projection.
ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
theorem PosSemidef.le_supportProj_of_norm_le_one (hA : A.PosSemidef)
    (hnorm : ‖A‖ ≤ 1) : A ≤ hA.supportProj := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    exact le_of_eq (Subsingleton.elim _ _)
  | inr hn =>
    have := hn
    change A ≤ hA.isHermitian.supportProj
    rw [hA.isHermitian.supportProj_eq_cfc]
    conv_lhs => rw [← cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
    refine cfc_mono (fun x hx ↦ ?_) (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)
    split_ifs with hx0
    · exact (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
    · simp only [not_not] at hx0
      simp [hx0]

/-- Replacing every positive term by its range projection preserves the
kernel of their sum. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460.
No bound on the norms of the original terms is required for this identity. -/
theorem PosSemidef.sum_supportProj_mulVec_eq_zero_iff
    {ι : Type*} [Fintype ι] {h : ι → Matrix n n ℂ}
    (hh : ∀ i, (h i).PosSemidef) (x : n → ℂ) :
    (∑ i, (hh i).supportProj) *ᵥ x = 0 ↔ (∑ i, h i) *ᵥ x = 0 := by
  have hp (i : ι) : ((hh i).supportProj).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      ((hh i).isHermitian.isStarProjection_supportProj).nonneg
  constructor
  · intro hx
    have hi (i : ι) := PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hp hx i
    have hz (i : ι) : h i *ᵥ x = 0 := by
      rw [← (hh i).mul_supportProj_self, ← Matrix.mulVec_mulVec, hi i, Matrix.mulVec_zero]
    simp only [Matrix.sum_mulVec, hz, Finset.sum_const_zero]
  · intro hx
    have hi (i : ι) := PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hh hx i
    have hz (i : ι) : (hh i).supportProj *ᵥ x = 0 :=
      (hh i).supportProj_mulVec_eq_zero_of_mulVec_eq_zero x (hi i)
    simp only [Matrix.sum_mulVec, hz, Finset.sum_const_zero]

end Matrix
