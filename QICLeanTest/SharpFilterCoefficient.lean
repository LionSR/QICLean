/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LogClipping

/-! Regression checks for the sharp coefficient in the polynomial-PEPS patch argument. -/

open Entropy

example (y : ℝ) : Real.cosh ((0 : ℝ) * y) - 1 = 0 ^ 2 * (Real.cosh y - 1) := by
  simp

example (y : ℝ) : Real.cosh ((1 : ℝ) * y) - 1 = 1 ^ 2 * (Real.cosh y - 1) := by
  simp

example (y : ℝ) : Real.cosh ((1 / 2 : ℝ) * y) - 1 ≤
    (1 / 2 : ℝ) ^ 2 * (Real.cosh y - 1) :=
  cosh_mul_sub_one_le_sq_mul (by norm_num) (by norm_num) y

-- Vanishing Schmidt probabilities require no logarithmic condition, even at nonzero t.
example (q t : ℝ) (hq : 0 ≤ q) :
    Real.sqrt (0 * q) * (Real.cosh t - 1) ≤ (1 / 2 : ℝ) ^ 2 / 2 * (0 + q) :=
  sqrt_mul_cosh_sub_one_le_sharp (by norm_num) le_rfl hq (by intro h; linarith)

example (p t : ℝ) (hp : 0 ≤ p) :
    Real.sqrt (p * 0) * (Real.cosh t - 1) ≤ (1 : ℝ) ^ 2 / 2 * (p + 0) :=
  sqrt_mul_cosh_sub_one_le_sharp le_rfl hp le_rfl (by intro _ h; linarith)

-- The old APIs do not assume nonnegative a. Equal positive probabilities permit a < 0.
example : Real.sqrt ((1 : ℝ) * 1) * (Real.cosh 0 - 1) ≤ (-2 : ℝ) ^ 2 / 2 * (1 + 1) :=
  sqrt_mul_cosh_sub_one_le_sharp (by norm_num) (by norm_num) (by norm_num)
    (by intro _ _; norm_num)

example {a p q t : ℝ} (ha : a ≤ 1 / 2) (hp : 0 < p) (hq : 0 < q)
    (ht : |t| ≤ a / 2 * |Real.log p - Real.log q|) :
    Real.sqrt (p * q) * (Real.cosh t - 1) ≤ 2 * a ^ 2 * (p + q) :=
  sqrt_mul_cosh_sub_one_le ha hp hq ht
