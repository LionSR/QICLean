/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A numerical coefficient in the rough lower comparison

The explicit rough lower estimate implies the comparison with coefficient
three when the parameter is at most one half. The entropy parameter is
arbitrary; its positive part is retained in the defect term.

This is a scalar consequence used in the lower comparison, rather than
an assertion about a physical state or its energy defect.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, `comparator:rough-lower`,
lines 153--169 and 585--651, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- The explicit rough lower expression dominates the expression with
coefficient three. No sign assumption is imposed on the entropy parameter.
Auxiliary to the area-law manuscript, `07-comparators.tex`,
`comparator:rough-lower`, lines 153--169 and 585--651. -/
theorem rough_lower_coefficient_three (S D h delta tau a : ℝ)
    (hD : 0 ≤ D) (hh : 0 ≤ h) (hdelta : 0 ≤ delta)
    (htau : 0 < tau) (ha : 0 < a) (haHalf : a ≤ 1 / 2) :
    4 * S - 2 * 3 * (tau * D + h / a) -
        3 * (delta / tau) * max 0 (2 * S) ≤
      2 * (2 * S - tau * (D + D) - (3 + 1 / a) * h -
        (delta / tau) * max 0 (2 * S)) := by
  have haInv : 2 ≤ 1 / a := (le_div_iff₀ ha).2 (by linarith only [haHalf])
  simp only [div_eq_mul_inv, one_mul] at haInv ⊢
  nlinarith only [mul_nonneg htau.le hD,
    mul_nonneg (by linarith only [haInv] : 0 ≤ 4 * a⁻¹ - 6) hh,
    mul_nonneg (mul_nonneg hdelta (inv_nonneg.mpr htau.le))
      (le_max_left 0 (2 * S))]

end Real
