/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolynomialFilterLogCount

/-!
# The logarithmic count at a fixed low-energy bandwidth

A fixed numerical count base and a capped initial width give an explicit
regularized logarithmic bound for the actual natural count. The physical
local dimension is unchanged. These are scalar estimates for ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1107–1128,
and the fixed-bandwidth convention in Assumption (LD), lines 281–284.
-/

namespace Real

/-- Multiplying the local dimension by one fixed integer gives the count
regularity used in the dyadic argument, with only an additive constant
in its logarithm. Auxiliary to ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem regularized_filter_count_base_bounds (q : ℕ) (hq : 2 ≤ q) :
    let M : ℕ := ⌈exp 100⌉₊
    let m := q * M
    q ≤ m ∧ 2 ≤ m ∧ 100 ≤ log (m : ℝ) ∧
      log (m : ℝ) ≤ log (q : ℝ) + 101 := by
  intro M m
  have hexp : 0 < exp (100 : ℝ) := exp_pos _
  have hexp1 : 1 ≤ exp (100 : ℝ) := by
    simpa only [exp_zero] using exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 100)
  have hMlow : exp (100 : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  have hM1R : (1 : ℝ) ≤ M := hexp1.trans hMlow
  have hM1 : 1 ≤ M := by exact_mod_cast hM1R
  have hMpos : (0 : ℝ) < M := zero_lt_one.trans_le hM1R
  have hMup : (M : ℝ) ≤ 2 * exp (100 : ℝ) :=
    (Nat.ceil_lt_add_one hexp.le).le.trans (by linarith only [hexp1])
  have hqm : q ≤ m := by
    simpa only [mul_one] using Nat.mul_le_mul_left q hM1
  have hm : 2 ≤ m := hq.trans hqm
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hq)
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogM : 100 ≤ log (M : ℝ) := by
    simpa only [log_exp] using log_le_log hexp hMlow
  have hlogMup : log (M : ℝ) ≤ 101 := by
    have hlog2 : log (2 : ℝ) ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
        log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    calc
      log (M : ℝ) ≤ log (2 * exp (100 : ℝ)) := log_le_log hMpos hMup
      _ = log 2 + 100 := by rw [log_mul (by norm_num) hexp.ne', log_exp]
      _ ≤ 101 := by linarith only [hlog2]
  have hlogm : log (m : ℝ) = log (q : ℝ) + log (M : ℝ) := by
    simp only [m, Nat.cast_mul, log_mul hqpos.ne' hMpos.ne']
  refine ⟨hqm, hm, ?_, ?_⟩
  · rw [hlogm]
    linarith only [hlogq, hlogM]
  · rw [hlogm]
    linarith only [hlogMup]

/-- Capping the initial deficit at half a fixed bandwidth changes the
inverse width by a bandwidth-dependent factor only. The logarithm is
bounded by a positive regularized logarithm, also when `v ≥ 1`.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1107–1128. -/
theorem capped_initial_filter_width_bounds (eta v : ℝ)
    (heta : 0 < eta) (hv : 0 < v) (hveta : v ≤ eta) :
    let vbar := min v (eta / 2)
    let g := min (vbar / 6) 1
    let B := max 12 eta
    0 < vbar ∧ v / 2 ≤ vbar ∧ 0 < g ∧ g ≤ 1 ∧
      1 / g ≤ B / v ∧ log (1 / g) ≤ log B + log (1 + 1 / v) := by
  intro vbar g B
  have hbar : 0 < vbar := lt_min hv (by positivity)
  have hbarLower : v / 2 ≤ vbar :=
    le_min (by linarith only [hv]) (by linarith only [hveta])
  have hg : 0 < g := lt_min (by positivity) zero_lt_one
  have hB : (12 : ℝ) ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hratio : 1 / g ≤ B / v := by
    apply (div_le_div_iff₀ hg hv).mpr
    by_cases hh : vbar / 6 ≤ 1
    · rw [show g = vbar / 6 from min_eq_left hh]
      have hmul := mul_le_mul_of_nonneg_right hB hbar.le
      nlinarith only [hbarLower, hmul]
    · rw [show g = 1 from min_eq_right (le_of_not_ge hh)]
      simpa only [one_mul, mul_one] using hveta.trans (le_max_right 12 eta)
  refine ⟨hbar, hbarLower, hg, min_le_right _ _, hratio, ?_⟩
  have hlog : log (1 / g) ≤ log B + log (1 / v) := by
    calc
      log (1 / g) ≤ log (B / v) := log_le_log (by positivity) hratio
      _ = log B + log (1 / v) := by
        rw [show B / v = B * (1 / v) by ring,
          log_mul hBpos.ne' (by positivity : (1 / v) ≠ 0)]
  have hlogv : log (1 / v) ≤ log (1 + 1 / v) :=
    log_le_log (by positivity) (by linarith)
  linarith only [hlog, hlogv]

/-- The cube of the actual initial natural count has the regularized
logarithmic bound used in the low-density dimension estimate. Its
coefficient depends only on the ceiling constant and fixed bandwidth,
before the local dimension and the deficit. Auxiliary to ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1107–1128. -/
theorem log_initial_low_density_count_le (C eta v : ℝ) (q : ℕ)
    (hC : 1 ≤ C) (heta : 0 < eta) (hv : 0 < v) (hveta : v ≤ eta)
    (hq : 2 ≤ q) :
    let m := q * ⌈exp 100⌉₊
    let vbar := min v (eta / 2)
    let g := min (vbar / 6) 1
    let u := 1 + log (m : ℝ) + log (1 / g)
    let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
    let D := (m * ell ^ 2) ^ (22 * ell)
    let B := max 12 eta
    let F := 102 + log B
    let K := 66 * (C + 1) * (6 + 2 * log (C + 1)) * B * F ^ 3
    let U := 1 + log (q : ℝ) + log (1 + 1 / v)
    0 < K ∧ q ≤ m ∧ 100 ≤ log (m : ℝ) ∧ 0 < (D : ℝ) ∧
      log ((D : ℝ) ^ 3) ≤ K / v * U ^ 3 := by
  intro m vbar g u ell D B F K U
  obtain ⟨hqm, hm, hlogm, hlogmup⟩ := regularized_filter_count_base_bounds q hq
  obtain ⟨_hbar, _hbarLower, hg, hg1, hratio, hlogg⟩ :=
    capped_initial_filter_width_bounds eta v heta hv hveta
  obtain ⟨_hlower, _hupper, _hell, hDpos, _hlinear, hbound⟩ :=
    polynomial_filter_count_bounds C m g hC hm hg hg1
  have hB : (12 : ℝ) ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hlogB : 0 ≤ log B := log_nonneg (by linarith only [hB])
  have hF : 1 ≤ F := by dsimp only [F]; linarith only [hlogB]
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  have hCpos : 0 < C + 1 := by linarith only [hC]
  have hlogC : 0 ≤ log (C + 1) := log_nonneg (by linarith only [hC])
  have hK : 0 < K := by dsimp only [K]; positivity
  have hlogq : 0 ≤ log (q : ℝ) :=
    log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hq))
  have hlogv : 0 ≤ log (1 + 1 / v) :=
    log_nonneg (le_add_of_nonneg_right (by positivity))
  have hu0 : 0 ≤ u := by
    have hlogg0 : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
    dsimp only [u]
    linarith only [hlogm, hlogg0]
  have hu : u ≤ F * U := by
    have hprod : 0 ≤ (F - 1) * (log (q : ℝ) + log (1 + 1 / v)) :=
      mul_nonneg (sub_nonneg.mpr hF) (add_nonneg hlogq hlogv)
    have hsum : u ≤ F + log (q : ℝ) + log (1 + 1 / v) := by
      dsimp only [u, F]
      linarith only [hlogmup, hlogg]
    dsimp only [U]
    nlinarith only [hsum, hprod]
  have hucube : u ^ 3 ≤ (F * U) ^ 3 := pow_le_pow_left₀ hu0 hu 3
  let P := 22 * (C + 1) * (6 + 2 * log (C + 1))
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨hK, hqm, hlogm, hDpos, ?_⟩
  calc
    log ((D : ℝ) ^ 3) = 3 * log (D : ℝ) := by rw [log_pow]; norm_num
    _ ≤ 3 * (P / g * u ^ 3) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = 3 * P * (1 / g) * u ^ 3 := by ring
    _ ≤ 3 * P * (B / v) * u ^ 3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (pow_nonneg hu0 3)
    _ ≤ 3 * P * (B / v) * (F * U) ^ 3 :=
      mul_le_mul_of_nonneg_left hucube (by positivity)
    _ = K / v * U ^ 3 := by dsimp only [P, K]; ring

end Real
