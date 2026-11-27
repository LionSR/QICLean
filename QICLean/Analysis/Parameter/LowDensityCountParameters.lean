/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Parameter.PolynomialFilterCounts
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The logarithmic count at a fixed low-energy bandwidth

A fixed numerical count base and a capped initial width give an explicit
regularized logarithmic bound for the actual natural count. The physical
local dimension is unchanged. These are scalar estimates for ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1107–1128,
and the fixed-bandwidth convention in Assumption (LD), lines 281–284.

It also contains the following results.

* `Real.low_density_entropy_cost_le`: the regularized low-density entropy coefficient.

## Main results

* `Real.low_density_dyadic_scale_growth`, `Real.low_density_dyadic_residual_le`: dyadic improvement
  of the truncation residual.
-/

namespace Real

section LowDensityCountParameters

section LowDensityCountParameters

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

end LowDensityCountParameters

section LowDensityEntropyParameters

/-!
## The regularized low-density entropy coefficient

The entropy obtained from the actual dyadic low-energy families contains
an initial-space contribution and a filter-count contribution. Both are
controlled by one regularized cubic logarithm at fixed bandwidth. This
numerical estimate supports ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`,
lines 1096–1105, and Proposition `prop:albootstrap-ld`, lines 1107–1128.
-/

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

end LowDensityEntropyParameters

end LowDensityCountParameters

section LowDensityDyadicScale

/-!
## Dyadic improvement of the truncation residual

Increasing the numerical counting base by powers of two increases the actual
ceiling window scale and decreases the physical truncation residual geometrically.
These auxiliary estimates support the accuracy refinement for the low-density
area law in ALVV, arXiv:1602.08828v2, proof of `thm:al-ld`, lines 1096–1128.
-/

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

end LowDensityDyadicScale

end Real
