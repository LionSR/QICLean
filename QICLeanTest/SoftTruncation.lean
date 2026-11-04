/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncation

/-! Boundary checks for the scalar soft truncation. -/

namespace Real.SoftTruncationTest

-- The zero input is fixed at every scale and every order.
example {t : ℝ} {m : ℕ} : softTruncation t m 0 = 0 := by
  simp [softTruncation]

-- At order one, the corrected logarithmic bound reduces to the scale itself.
example {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    softTruncation t 1 x ≤ t := by
  have h := (softTruncation_bounds t 1 x ht (by norm_num) hx).2.2.2
  simpa using h

-- The paper's printed `t * log m` bound fails already at `t = m = x = 1`.
example : 0 < softTruncation 1 1 1 := by
  simp only [softTruncation, Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero,
    div_one, one_mul]
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact sub_pos.mpr hexp

end Real.SoftTruncationTest
