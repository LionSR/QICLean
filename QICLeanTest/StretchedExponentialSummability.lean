/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StretchedExponentialSummability

/-! Fractional decay, nonintegral cutoffs, geometric normalization, and boundary failures. -/

open scoped BigOperators

namespace StretchedExponentialSummabilityTest

-- A fourth polynomial moment is still summable at square-root decay.
example : Summable (fun n : ℕ ↦
    (1 + (n : ℝ)) ^ 4 * Real.exp (-3 * (n : ℝ) ^ (1 / 2 : ℝ))) :=
  Real.summable_nat_pow_mul_exp_neg_mul_rpow 4 (by norm_num) (by norm_num)

-- A real cutoff of 5/2 keeps precisely the radii starting at three.
example :
    (∑' n : {n : ℕ // (5 / 2 : ℝ) ≤ (n : ℝ)},
      (1 + (n.val : ℝ)) ^ 4 * Real.exp (-3 * (n.val : ℝ) ^ (1 / 2 : ℝ))) ≤
      (∑' n : ℕ, (1 + (n : ℝ)) ^ 4 * Real.exp (-(3 / 2) * (n : ℝ) ^ (1 / 2 : ℝ))) *
        Real.exp (-(3 / 2) * (5 / 2 : ℝ) ^ (1 / 2 : ℝ)) := by
  exact Real.tsum_nat_pow_mul_exp_neg_mul_rpow_tail_le 4
    (by norm_num) (by norm_num) (by norm_num)

-- The zero-degree, exponent-one specialization has the usual geometric sum.
example :
    (∑' n : ℕ, (1 + (n : ℝ)) ^ 0 * Real.exp (-1 * (n : ℝ) ^ (1 : ℝ))) =
      (1 - Real.exp (-1))⁻¹ := by
  calc
    _ = ∑' n : ℕ, Real.exp (-1) ^ n := by
      apply tsum_congr
      intro n
      rw [pow_zero, one_mul, Real.rpow_one, mul_comm (-1), Real.exp_nat_mul]
    _ = _ := tsum_geometric_of_lt_one (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))

-- The radius-zero summand supplies one even for a fractional exponent.
example : 1 ≤ ∑' n : ℕ,
    (1 + (n : ℝ)) ^ 4 * Real.exp (-3 * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  exact Real.one_le_tsum_nat_pow_mul_exp_neg_mul_rpow 4 (by norm_num) (by norm_num)

-- At exponent zero every degree-zero term is exp(-3), so summability fails.
example : ¬ Summable (fun n : ℕ ↦
    (1 + (n : ℝ)) ^ 0 * Real.exp (-3 * (n : ℝ) ^ (0 : ℝ))) := by
  simp [summable_const_iff, Real.exp_ne_zero]

-- Positive exponent alone does not suffice when the decay rate vanishes.
example : ¬ Summable (fun n : ℕ ↦
    (1 + (n : ℝ)) ^ 0 * Real.exp (0 * (n : ℝ) ^ (1 / 2 : ℝ))) := by
  simp [summable_const_iff]

end StretchedExponentialSummabilityTest
