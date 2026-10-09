/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum

/-!
# A common mass in five exponential moment bounds

A common nonnegative mass appears once after taking the product of five
fifth moments. The zero-mass case is included, without logarithms of that
mass or normalization of the underlying positive measure.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 520--560,
`comparator:merge-moments` and `comparator:component-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace Real

/-- Five nonnegative moments with a common exponential bound retain the
common mass once in their geometric mean. Source: `07-comparators.tex`,
lines 520--560. The common mass may vanish. -/
theorem prod_five_rpow_le_common_exp
    (M A : Fin 5 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ i, 0 ≤ M i) (hbound : ∀ i, M i ≤ c * exp (A i)) :
    (∏ i, M i ^ (1 / 5 : ℝ)) ≤ c * exp ((∑ i, A i) / 5) := by
  calc
    (∏ i, M i ^ (1 / 5 : ℝ)) ≤
        ∏ i, c ^ (1 / 5 : ℝ) * exp (A i * (1 / 5 : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact rpow_nonneg (hM i) _
      · intro i _
        simpa only [mul_rpow hc (exp_pos (A i)).le, ← exp_mul] using
          rpow_le_rpow (hM i) (hbound i) (by norm_num : (0 : ℝ) ≤ 1 / 5)
    _ = (c ^ (1 / 5 : ℝ)) ^ 5 * exp ((∑ i, A i) * (1 / 5 : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← exp_sum, ← Finset.sum_mul]
    _ = c * exp ((∑ i, A i) / 5) := by
      rw [← rpow_mul_natCast hc]
      norm_num [div_eq_mul_inv]

end Real
