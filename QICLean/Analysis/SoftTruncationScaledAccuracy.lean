/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncationAccuracy

/-!
# A compatible order for soft truncation at three times its order

The logarithmic order controls both the reverse physical cutoff and the residual while leaving
all heat times strictly below the cluster threshold. Supporting the corrected moment route to
ALVV, arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268.
-/

namespace Real

/-- One explicit order controls the correction, the reverse cutoff and the requested residual
when scale is three times order. Supporting the corrected moment route to ALVV,
arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268. -/
theorem exists_softTruncation_scaled_order_of_residual_budget
    (eta rho : ℝ) (heta : 0 ≤ eta) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ m : ℕ, m = ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ ∧
      0 < m ∧ 10 ≤ (3 * (m : ℝ)) / 2 ∧
      let alpha := (3 * (m : ℝ)) / 2 * (1 / 2 : ℝ) ^ m
      0 ≤ alpha ∧ alpha ≤ 3 / 4 ∧ 17 + eta + alpha ≤ (3 * (m : ℝ)) / 2 ∧
      80 * exp ((17 + eta + alpha) / 8 - (3 * (m : ℝ)) / 16) ≤ rho := by
  let m := ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊
  have hlog : 0 ≤ log (80 / rho) := log_nonneg ((one_le_div hrho).mpr (by linarith))
  have hmcast : 12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho) ≤
      (m : ℝ) := Nat.le_ceil _
  have hm : 0 < m := by
    have hp : (0 : ℝ) < m := by linarith only [hmcast, heta, hlog]
    exact_mod_cast hp
  have ha := softTruncation_order_error_le_one_fourth m hm
  have ha3 : (3 * (m : ℝ)) / 2 * (1 / 2 : ℝ) ^ m ≤ 3 / 4 := by linarith only [ha]
  refine ⟨m, rfl, hm, by linarith only [hmcast, heta, hlog], ?_⟩
  intro alpha
  refine ⟨by dsimp only [alpha]; positivity, ha3, ?_, ?_⟩
  · change 17 + eta + (3 * (m : ℝ)) / 2 * (1 / 2 : ℝ) ^ m ≤ _
    linarith only [hmcast, hlog, ha3]
  · calc
      _ ≤ 80 * exp (-log (80 / rho)) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        change (17 + eta + (3 * (m : ℝ)) / 2 * (1 / 2 : ℝ) ^ m) / 8 -
          (3 * (m : ℝ)) / 16 ≤ _
        linarith only [hmcast, ha3]
      _ = rho := by
        rw [exp_neg, exp_log (div_pos (by norm_num) hrho)]
        field_simp

end Real
