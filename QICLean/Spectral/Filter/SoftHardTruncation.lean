/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Filter.EnergyTruncation
import QICLean.Analysis.Real.SoftTruncation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Comparing soft and hard spectral truncation

For a positive semidefinite matrix, soft truncation lies between the original
matrix and hard truncation at half the scale, up to an exponentially small
scalar error. Both truncations are functions of the same matrix.

This is an auxiliary comparison for the truncations in ALVV,
arXiv:1602.08828v2, Definitions `def:hard-trunc` and `def:soft-trunc`,
lines 873–886 and 1178–1185. It does not assert the printed uniform energy
estimate in equation `eq:exp-approx-0` or a spectral-subspace approximation.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

/-- On a positive semidefinite matrix, soft truncation dominates hard
truncation at half its scale up to the scalar error `(t / 2) * (1 / 2)^m`,
and lies below the original matrix. Auxiliary to ALVV, arXiv:1602.08828v2,
Definitions `def:hard-trunc` and `def:soft-trunc`, lines 873–886 and 1178–1185. -/
lemma PosSemidef.softTruncation_hard_bounds
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 < t) (hm : 1 ≤ m) :
    energyTruncation A (t / 2) - (((t / 2) * (1 / 2 : ℝ) ^ m : ℝ) : ℂ) • 1 ≤
        cfc (Real.softTruncation t m) A ∧
      cfc (Real.softTruncation t m) A ≤ A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  constructor
  · have hconst : cfc (fun _ : ℝ ↦ (t / 2) * (1 / 2 : ℝ) ^ m) A =
        (((t / 2) * (1 / 2 : ℝ) ^ m : ℝ) : ℂ) • 1 := by
      rw [cfc_const _ A hA.isHermitian.isSelfAdjoint,
        Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    rw [energyTruncation, ← hconst, ← cfc_sub _ _ A (hc _) (hc _)]
    exact cfc_mono (fun x hx ↦
      (Real.softTruncation_hard_bounds t m x ht hm
        (spectrum_nonneg_of_nonneg hA.nonneg hx)).1) (hc _) (hc _)
  · conv_rhs => rw [← cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
    exact cfc_mono (fun x hx ↦
      (Real.softTruncation_hard_bounds t m x ht hm
        (spectrum_nonneg_of_nonneg hA.nonneg hx)).2) (hc _) (hc _)

end Matrix

section SoftTruncationOperatorBounds

/-!
# An operator cap for soft truncation

The scalar bound for the actual finite soft function gives the same
upper bound in the matrix order. The scale and order are independent.
This is an auxiliary to ALVV, arXiv:1602.08828v2, lines 1152–1173.
**Local fix (harmonic cap):** The factor `1 + log m` is retained; the printed factor
`log m` is false. See
`docs/paper-gaps/alvv16_soft_truncation_log_bound.tex`.
-/

open scoped ComplexOrder MatrixOrder

namespace Matrix

/-- The actual soft function of a positive matrix is bounded above by
its scale times the corrected logarithmic harmonic cap. ALVV,
arXiv:1602.08828v2, lines 1152–1173, with the correction documented in
`docs/paper-gaps/alvv16_soft_truncation_log_bound.tex`. -/
theorem PosSemidef.cfc_softTruncation_le_scalar
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 < t) (hm : 1 ≤ m) :
    cfc (Real.softTruncation t m) A ≤ (t * (1 + Real.log (m : ℝ))) • 1 := by
  calc
    cfc (Real.softTruncation t m) A ≤
        cfc (fun _ : ℝ ↦ t * (1 + Real.log (m : ℝ))) A := by
      apply cfc_mono
      · intro x hx
        exact (Real.softTruncation_bounds t m x ht hm
          (spectrum_nonneg_of_nonneg hA.nonneg hx)).2.2.2
      · exact A.finite_real_spectrum.continuousOn _
      · exact A.finite_real_spectrum.continuousOn _
    _ = _ := by
      rw [cfc_const _ A hA.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

end Matrix

end SoftTruncationOperatorBounds
