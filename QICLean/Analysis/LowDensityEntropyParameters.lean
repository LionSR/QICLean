/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowDensityCountParameters
import Mathlib.Tactic.GCongr

/-!
# The regularized low-density entropy coefficient

The entropy obtained from the actual dyadic low-energy families contains
an initial-space contribution and a filter-count contribution. Both are
controlled by one regularized cubic logarithm at fixed bandwidth. This
numerical estimate supports ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`,
lines 1096–1105, and Proposition `prop:albootstrap-ld`, lines 1107–1128.
-/

namespace Real

/-- The explicit entropy costs at a capped initial width are bounded by
one bandwidth-dependent coefficient times the regularized cubic logarithm.
The ground-space multiplicity is absent from this coefficient, preserving
its coefficient one in the separate logarithmic dimension term. Auxiliary
to ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem low_density_entropy_cost_le {eta v Kb Cf : ℝ} {q : ℕ}
    (heta : 0 < eta) (hv : 0 < v) (hveta : v ≤ eta)
    (hKb : 0 < Kb) (hCf : 100 ≤ Cf) (hq : 2 ≤ q) :
    let b := min v (eta / 2)
    let g := min (b / 6) 1
    let m := q * ⌈exp 100⌉₊
    let U := 1 + log (q : ℝ) + log (1 + 1 / v)
    let B := max 12 eta
    let F := 102 + log B
    let P := 14872 * (Cf + 1) * (6 + 2 * log (Cf + 1))
    let K := 108 * Kb + P * B * F ^ 3 + 54 * eta
    0 < K ∧
      Kb / (b / 2) * (1 + log (q : ℝ) + log (1 + 1 / (b / 2))) ^ 3 +
        P / g * (1 + log (m : ℝ) + log (1 / g)) ^ 3 + 54 * log 2 ≤
      K / v * U ^ 3 := by
  intro b g m U B F P K
  obtain ⟨hb, hbLower, hg, hg1, hratio, hlogg⟩ :=
    capped_initial_filter_width_bounds eta v heta hv hveta
  obtain ⟨_hqm, _hm, hlogm, hlogmup⟩ := regularized_filter_count_base_bounds q hq
  have hlogq : 0 ≤ log (q : ℝ) :=
    log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hq))
  have hlogv : 0 ≤ log (1 + 1 / v) :=
    log_nonneg (le_add_of_nonneg_right (by positivity))
  have hU : 1 ≤ U := by dsimp only [U]; linarith only [hlogq, hlogv]
  have hlogB : 0 ≤ log B :=
    log_nonneg ((by norm_num : (1 : ℝ) ≤ 12).trans (le_max_left 12 eta))
  have hF : 1 ≤ F := by dsimp only [F]; linarith only [hlogB]
  have hlogCf : 0 ≤ log (Cf + 1) := log_nonneg (by linarith only [hCf])
  have hP : 0 < P := mul_pos
    (mul_pos (by norm_num) (by linarith only [hCf])) (by linarith only [hlogCf])
  have hK : 0 < K := by dsimp only [K, F, B]; positivity
  have hbinv : 1 / (b / 2) ≤ 4 / v :=
    (div_le_div_iff₀ (by positivity : 0 < b / 2) hv).mpr
      (by dsimp only [b]; linarith only [hbLower])
  have hlogb : log (1 + 1 / (b / 2)) ≤ log 4 + log (1 + 1 / v) := by
    calc
      _ ≤ log (4 * (1 + 1 / v)) :=
        log_le_log (by positivity) (by
          convert add_le_add (by norm_num : (1 : ℝ) ≤ 4) hbinv using 1
          ring)
      _ = _ := log_mul (by norm_num) (by positivity)
  have hlog2 : log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 : log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith only [hlog2]
  have hbU : 1 + log (q : ℝ) + log (1 + 1 / (b / 2)) ≤ 3 * U := by
    dsimp only [U]
    linarith only [hlogb, hlog4, hlogq, hlogv]
  have hmU : 1 + log (m : ℝ) + log (1 / g) ≤ F * U := by
    calc
      _ ≤ F + log (q : ℝ) + log (1 + 1 / v) := by
        dsimp only [m, g, b, F, B]
        linarith only [hlogmup, hlogg]
      _ ≤ F * U := by
        dsimp only [U]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hF) (add_nonneg hlogq hlogv)]
  have hbBase0 : 0 ≤ 1 + log (q : ℝ) + log (1 + 1 / (b / 2)) :=
    add_nonneg (by linarith only [hlogq])
      (log_nonneg (le_add_of_nonneg_right (by positivity)))
  have hbCost : Kb / (b / 2) * (1 + log (q : ℝ) + log (1 + 1 / (b / 2))) ^ 3 ≤
      108 * Kb / v * U ^ 3 := by
    calc
      _ ≤ (Kb * (4 / v)) * (3 * U) ^ 3 := mul_le_mul
        (by simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hbinv hKb.le)
        (pow_le_pow_left₀ hbBase0 hbU 3) (pow_nonneg hbBase0 3) (by positivity)
      _ = _ := by ring
  have hmBase0 : 0 ≤ 1 + log (m : ℝ) + log (1 / g) := by
    have hh : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
    change 100 ≤ log (m : ℝ) at hlogm
    linarith only [hlogm, hh]
  change 1 / g ≤ B / v at hratio
  have hmCost : P / g * (1 + log (m : ℝ) + log (1 / g)) ^ 3 ≤
      (P * B * F ^ 3) / v * U ^ 3 := by
    calc
      _ ≤ (P * (B / v)) * (F * U) ^ 3 := mul_le_mul
        (by simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hratio hP.le)
        (pow_le_pow_left₀ hmBase0 hmU 3) (pow_nonneg hmBase0 3)
        (by dsimp only [B]; positivity)
      _ = _ := by ring
  have hconst : 54 * log 2 ≤ 54 * eta / v * U ^ 3 := by
    calc
      _ ≤ 54 * 1 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ ≤ 54 * (eta / v * U ^ 3) := mul_le_mul_of_nonneg_left
        (one_le_mul_of_one_le_of_one_le ((one_le_div hv).mpr hveta) (one_le_pow₀ hU)) (by norm_num)
      _ = _ := by ring
  refine ⟨hK, ?_⟩
  calc
    _ ≤ (108 * Kb / v * U ^ 3 + (P * B * F ^ 3) / v * U ^ 3) +
        54 * eta / v * U ^ 3 := add_le_add (add_le_add hbCost hmCost) hconst
    _ = _ := by dsimp only [K]; ring

end Real
