/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exponential bounds for complete-window geometric decay

A geometric factor counted in complete fixed-width windows is bounded by an exponential
in the original interval length. The lower bound on the geometric base controls the
one-window rounding factor uniformly.
-/

namespace Real

/-- For a base in `[1/2,1)`, counting only complete windows loses at most a factor two
relative to the exponential rate in the full interval length. -/
theorem pow_nat_div_le_two_mul_exp (s n : ℕ) (hs : 0 < s) (ρ : ℝ)
    (hρhalf : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) :
    ρ ^ (n / s) ≤ 2 * Real.exp (-((-Real.log ρ / s) * n)) := by
  have hρ0 : 0 < ρ := by linarith
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have ht : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ0 hρ1)
  have hn : (n : ℝ) ≤ (n / s : ℕ) * s + s := by
    have hd := Nat.div_add_mod n s
    rw [Nat.mul_comm s (n / s)] at hd
    have hm := Nat.mod_lt n hs
    exact_mod_cast (show n ≤ n / s * s + s by omega)
  have hf : (n : ℝ) / s ≤ (n / s : ℕ) + 1 := by
    apply (div_le_iff₀ hsR).mpr
    nlinarith
  have hb := mul_le_mul_of_nonneg_left hf ht.le
  have hinv : ρ⁻¹ ≤ 2 := by
    simpa only [one_div] using (one_div_le hρ0 two_pos).mpr hρhalf
  calc ρ ^ (n / s) = Real.exp ((n / s : ℕ) * Real.log ρ) := by
        rw [Real.exp_nat_mul, Real.exp_log hρ0]
    _ ≤ Real.exp (-Real.log ρ + -((-Real.log ρ / s) * n)) := by
        apply Real.exp_le_exp.mpr
        calc (n / s : ℕ) * Real.log ρ = -((-Real.log ρ) * (n / s : ℕ)) := by ring
          _ ≤ -Real.log ρ - (-Real.log ρ) * ((n : ℝ) / s) := by nlinarith
          _ = _ := by ring
    _ = ρ⁻¹ * Real.exp (-((-Real.log ρ / s) * n)) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hρ0]
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le

end Real
