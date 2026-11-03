/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dyadic improvement of the truncation residual

Increasing the numerical counting base by powers of two increases the actual
ceiling window scale and decreases the physical truncation residual geometrically.
These auxiliary estimates support the accuracy refinement for the low-density
area law in ALVV, arXiv:1602.08828v2, proof of `thm:al-ld`, lines 1096–1128.
-/

namespace Real

/-- The actual ceiling scale increases by at least sixty-four sites at each
dyadic refinement. Auxiliary to the low-density accuracy refinement in ALVV,
arXiv:1602.08828v2, proof of `thm:al-ld`, lines 1096–1128. -/
theorem low_density_dyadic_scale_growth {C u g : ℝ}
    (hC : 100 ≤ C) (hu : 1 ≤ u) (hg : 0 < g) (hg1 : g ≤ 1) (i : ℕ) :
    (⌈C * u ^ 2 / g⌉₊ : ℝ) + 64 * i ≤
      (⌈C * (u + i * log 2) ^ 2 / g⌉₊ : ℝ) := by
  have hlog : (1 / 2 : ℝ) ≤ log 2 := by
    have hh := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hshift : u + (i : ℝ) / 2 ≤ u + i * log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg i)]
  have hinc : (i : ℝ) ≤ (u + i * log 2) ^ 2 - u ^ 2 := by
    have hs := pow_le_pow_left₀
      (by linarith [show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i] :
        0 ≤ u + (i : ℝ) / 2) hshift 2
    nlinarith [mul_nonneg (by linarith : 0 ≤ u - 1) (Nat.cast_nonneg i)]
  have hcoef : 100 ≤ C / g := (le_div_iff₀ hg).mpr (by linarith)
  have hmul : 64 * (i : ℝ) ≤ (C / g) * ((u + i * log 2) ^ 2 - u ^ 2) :=
    mul_le_mul (by linarith : 64 ≤ C / g) hinc (Nat.cast_nonneg i) (by linarith)
  have hbase : C * u ^ 2 / g + ((64 * i : ℕ) : ℝ) ≤
      C * (u + i * log 2) ^ 2 / g := by
    calc
      _ = (C / g) * u ^ 2 + 64 * (i : ℝ) := by push_cast; ring
      _ ≤ (C / g) * u ^ 2 + (C / g) * ((u + i * log 2) ^ 2 - u ^ 2) :=
        add_le_add le_rfl hmul
      _ = _ := by ring
  have hceil := Nat.ceil_le_ceil hbase
  rw [Nat.ceil_add_natCast (div_nonneg (mul_nonneg (by linarith) (sq_nonneg u)) hg.le)]
    at hceil
  exact_mod_cast hceil

/-- The exponential truncation residual decreases geometrically at the actual
ceiling scales. Auxiliary to the low-density accuracy refinement in ALVV,
arXiv:1602.08828v2, proof of `thm:al-ld`, lines 1096–1128. -/
theorem low_density_dyadic_residual_le {C u g : ℝ}
    (hC : 100 ≤ C) (hu : 1 ≤ u) (hg : 0 < g) (hg1 : g ≤ 1) (i : ℕ) (eta : ℝ) :
    exp (-((⌈C * (u + i * log 2) ^ 2 / g⌉₊ : ℝ) - eta) / 8) ≤
      exp (-((⌈C * u ^ 2 / g⌉₊ : ℝ) - eta) / 8) / (2 : ℝ) ^ (4 * i) := by
  have hscale := low_density_dyadic_scale_growth hC hu hg hg1 i
  have hlog : log (2 : ℝ) ≤ 1 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : (2 : ℝ) ^ (4 * i) = exp (((4 * i : ℕ) : ℝ) * log 2) := by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _), hpow,
    ← exp_add, exp_le_exp]
  push_cast
  nlinarith only [hscale, mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg i)]

end Real
