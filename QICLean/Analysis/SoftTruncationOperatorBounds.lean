/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

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
