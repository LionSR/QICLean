/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A simultaneous soft-family calibration before the volume

A single large natural parameter determines the window, Taylor order,
truncation scale, filter degree and residual cutoffs. The count and precision
budgets are then evaluated at those same choices. No parameter is defined
through a subsequently chosen count.

This is a scalar auxiliary for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, `t:aisefficient` and `fig:merge-prime`, lines
1262–1268, 1373–1420 and 1664–1673. The calibration is intended for
half-dimension resampling followed by original-target trimming. It does
not establish the sample-once iteration, the printed fourth-order
parameter choice, the Generate algorithm or a quasi-polynomial running-time bound.
For gap width `0 < w ≤ 1`, gap `w²/2` and budgets `(24,10,10)`, the natural
scale in this corrected calibration is bounded by a constant depending only
on the local dimension times `(1 + w⁻¹)^4`.

This is a new sufficient scalar calibration; it replaces no step of the
source. The source specifies the window and filter scales of its
fourth-order soft truncation in terms of the gap, lines 1373–1420. Here one
natural scale `u` fixes `ℓ = u^8`, `m = u^10`, `t = 3m`, `k = u^16` and
`T = u^9`, and the family count and the precision are evaluated at that same
`u`, so no tolerance is chosen before a count that would change it. The
repeated-resampling variant in which such a calibration can be used is
described in `docs/paper-gaps/alvv16_bootstrap_constants.tex`.
-/

open Filter Topology

namespace Real

/-- A quadratic threshold in the normalized coefficients suffices for every positive
natural exponent. This estimate quantifies the corrected scalar calibration. -/
theorem affine_log_le_nat_pow_of_threshold (a b : ℝ) {ε x : ℝ} {p : ℕ}
    (hp : 0 < p) (hε : 0 < ε) (hx : 1 ≤ x)
    (h : ((|a| + 2 * |b|) / ε) ^ 2 ≤ x) :
    a + b * log x ≤ ε * x ^ p := by
  have hs := sq_sqrt (zero_le_one.trans hx)
  have hs1 : 1 ≤ sqrt x := by simpa using sqrt_le_sqrt hx
  have hl := log_le_sub_one_of_pos (zero_lt_one.trans_le hs1)
  rw [log_sqrt (zero_le_one.trans hx)] at hl
  have hc : (|a| + 2 * |b|) / ε ≤ sqrt x := by
    nlinarith only [h, hs, sqrt_nonneg x, sq_nonneg ((|a| + 2 * |b|) / ε - sqrt x)]
  have hcoef := (div_le_iff₀ hε).mp hc
  calc
    a + b * log x ≤ |a| * sqrt x + |b| * (2 * sqrt x) := by
      gcongr
      · exact (le_abs_self a).trans (le_mul_of_one_le_right (abs_nonneg a) hs1)
      · exact log_nonneg hx
      · exact le_abs_self b
      · linarith only [hl]
    _ = (|a| + 2 * |b|) * sqrt x := by ring
    _ ≤ (sqrt x * ε) * sqrt x := mul_le_mul_of_nonneg_right hcoef (sqrt_nonneg x)
    _ = ε * x := by nlinarith only [congrArg (ε * ·) hs]
    _ ≤ ε * x ^ p := mul_le_mul_of_nonneg_left (le_self_pow₀ hx hp.ne') hε.le

private theorem soft_family_sqrt_gain {u g H : ℝ}
    (hu : 0 ≤ u) (hg : 0 < g) (hH : 0 < H) (hbound : H ≤ u ^ 12)
    (hgu : 1 ≤ g * u ^ 2) :
    u ^ 9 ≤ 4 * u ^ 16 * sqrt ((g / 2) / H) := by
  have hscaled : u ^ 30 ≤ g * u ^ 32 := by
    calc
      u ^ 30 = u ^ 30 * 1 := (mul_one _).symm
      _ ≤ u ^ 30 * (g * u ^ 2) :=
        mul_le_mul_of_nonneg_left hgu (pow_nonneg hu _)
      _ = g * u ^ 32 := by ring
  have hsquare : (4 * u ^ 16 * sqrt ((g / 2) / H)) ^ 2 = 8 * g * u ^ 32 / H := by
    rw [mul_pow, mul_pow, sq_sqrt (by positivity)]
    ring
  apply (sq_le_sq₀ (pow_nonneg hu _) (by positivity)).mp
  rw [hsquare]
  apply (le_div_iff₀ hH).mpr
  calc
    (u ^ 9) ^ 2 * H = u ^ 18 * H := by ring
    _ ≤ u ^ 18 * u ^ 12 := mul_le_mul_of_nonneg_left hbound (pow_nonneg hu _)
    _ = u ^ 30 := by ring
    _ ≤ g * u ^ 32 := hscaled
    _ ≤ 8 * g * u ^ 32 := by nlinarith only [mul_nonneg hg.le (pow_nonneg hu 32)]

private theorem exp_le_inv_powers_of_log_budget {D M eta x : ℝ} {a b : ℕ}
    (hD : 0 < D) (hM : 0 < M) (heta : 0 < eta)
    (hbudget : (a : ℝ) * log D + (b : ℝ) * log M + x ≤ log eta) :
    exp x ≤ eta / (D ^ a * M ^ b) := by
  have hx : x ≤ log eta - ((a : ℝ) * log D + (b : ℝ) * log M) := by
    linarith only [hbudget]
  refine (exp_le_exp.mpr hx).trans_eq ?_
  rw [exp_sub, exp_log heta, exp_add, exp_nat_mul, exp_nat_mul, exp_log hD, exp_log hM]

private theorem soft_family_budgets_of_log_bound
    {u g D M xi : ℝ} {m a b c : ℕ}
    (hu : 1 ≤ u) (hlogu : 1 ≤ log u) (hg : 0 < g)
    (hD : 1 ≤ D) (hM : 1 ≤ M) (hm : (m : ℝ) = u ^ 10)
    (hupper : M + xi + 4 + g ≤ u ^ 12) (hxi : 0 < xi)
    (hgu : 1 ≤ g * u ^ 2)
    (hbudget : ((a : ℝ) + 12) * log D + ((b : ℝ) + c) * log M +
      (200 + g + |log (g / 2000000)|) ≤ u ^ 9 / 64) :
    let tau := 1 / (D ^ a * M ^ b)
    3 * (32 * exp (-(u ^ 9 - g / 40 - 24) / 8) +
        ((3 * (m : ℝ)) / m) * (u ^ 9 / (3 * m)) ^ m) ≤ tau * g / 1000000 ∧
      3 * (32 * exp (-(u ^ 9 - 156 - 2 * g) / 8) +
        ((3 * (m : ℝ)) / m) * (u ^ 9 / (3 * m)) ^ m) ≤ tau * g / 1000000 ∧
      (2 * exp (-2 * u ^ 16 * sqrt ((g / 2) / (M + xi + 4 + g)))) ^ 2 ≤
        1 / (D ^ 12 * M ^ c) := by
  intro tau
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hlogD : 0 ≤ log D := log_nonneg hD
  have hlogM : 0 ≤ log M := log_nonneg hM
  have hu9 : 0 ≤ u ^ 9 := pow_nonneg hu0.le _
  have hmp : 0 < (m : ℝ) := by rw [hm]; positivity
  have hcost : (a : ℝ) * log D + (b : ℝ) * log M +
      (200 + g + |log (g / 2000000)|) ≤ u ^ 9 / 64 := by
    nlinarith only [hbudget, hlogD, mul_nonneg (Nat.cast_nonneg c) hlogM]
  have hconstExp : log 96 + (156 + 2 * g) / 8 - log (g / 2000000) ≤
      200 + g + |log (g / 2000000)| := by
    have hlog96 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 96)
    linarith only [hlog96, neg_le_abs (log (g / 2000000)), hg]
  have hExp : 96 * exp (-(u ^ 9 - 156 - 2 * g) / 8) ≤
      (g / 2000000) / (D ^ a * M ^ b) := by
    have he := exp_le_inv_powers_of_log_budget (a := a) (b := b) hD0 hM0
      (by positivity : 0 < g / 2000000)
      (x := log 96 + (156 + 2 * g - u ^ 9) / 8)
      (by linarith only [hcost, hconstExp, hu9])
    simpa only [exp_add, exp_log (by norm_num : (0 : ℝ) < 96),
      show (156 + 2 * g - u ^ 9) / 8 = -(u ^ 9 - 156 - 2 * g) / 8 by ring] using he
  have hlog3u : 1 ≤ log (3 * u) := hlogu.trans
    (log_le_log hu0 (by linarith only [hu0]))
  have hm9 : u ^ 9 ≤ (m : ℝ) := by
    rw [hm]
    calc
      u ^ 9 = u ^ 9 * 1 := (mul_one _).symm
      _ ≤ u ^ 9 * u := mul_le_mul_of_nonneg_left hu hu9
      _ = u ^ 10 := by ring
  have hTaylor : 9 * (1 / (3 * u)) ^ m ≤ (g / 2000000) / (D ^ a * M ^ b) := by
    have hlog9 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    have htime : u ^ 9 ≤ (m : ℝ) * log (3 * u) :=
      hm9.trans (by simpa using mul_le_mul_of_nonneg_left hlog3u hmp.le)
    have he := exp_le_inv_powers_of_log_budget (a := a) (b := b) hD0 hM0
      (by positivity : 0 < g / 2000000)
      (x := log 9 - (m : ℝ) * log (3 * u))
      (by linarith only [hcost, hlog9, neg_le_abs (log (g / 2000000)), hg, htime, hu9])
    have hid : exp (log 9 - (m : ℝ) * log (3 * u)) = 9 * (1 / (3 * u)) ^ m := by
      rw [sub_eq_add_neg, exp_add, exp_log (by norm_num : (0 : ℝ) < 9), exp_neg,
        exp_nat_mul, exp_log (by positivity : 0 < 3 * u)]
      simp only [one_div, inv_pow]
    exact hid ▸ he
  have hratio : u ^ 9 / (3 * (m : ℝ)) = 1 / (3 * u) := by
    rw [hm]
    field_simp [hu0.ne']
  have hR : 3 * (32 * exp (-(u ^ 9 - 156 - 2 * g) / 8) +
        ((3 * (m : ℝ)) / m) * (u ^ 9 / (3 * m)) ^ m) ≤ tau * g / 1000000 := by
    rw [mul_div_cancel_right₀ 3 hmp.ne', hratio]
    have hsum := add_le_add hExp hTaylor
    dsimp only [tau]
    convert hsum using 1 <;> ring
  refine ⟨?_, hR, ?_⟩
  · refine le_trans ?_ hR
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 32)
    apply exp_le_exp.mpr
    linarith only [hg]
  have hcostCheby : 12 * log D + (c : ℝ) * log M + log 4 ≤ u ^ 9 / 64 := by
    have hlog4 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    nlinarith only [hbudget, hlog4, hg, abs_nonneg (log (g / 2000000)),
      mul_nonneg (Nat.cast_nonneg a) hlogD, mul_nonneg (Nat.cast_nonneg b) hlogM]
  have hgain : u ^ 9 ≤ 4 * u ^ 16 * sqrt ((g / 2) / (M + xi + 4 + g)) :=
    soft_family_sqrt_gain hu0.le hg (by positivity) hupper hgu
  have he := exp_le_inv_powers_of_log_budget (a := 12) (b := c) hD0 hM0
    (by norm_num : (0 : ℝ) < 1)
    (x := log 4 - 4 * u ^ 16 * sqrt ((g / 2) / (M + xi + 4 + g)))
    (by norm_num only [Nat.cast_ofNat, log_one]
        linarith only [hcostCheby, hgain, hu9])
  have hid : (2 * exp (-2 * u ^ 16 * sqrt ((g / 2) / (M + xi + 4 + g)))) ^ 2 =
      exp (log 4 - 4 * u ^ 16 * sqrt ((g / 2) / (M + xi + 4 + g))) := by
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← exp_nat_mul,
      sub_eq_add_neg, exp_add, exp_log (by norm_num : (0 : ℝ) < 4)]
    congr 2
    ring
  exact hid.symm ▸ he

private theorem soft_family_log_bounds {q u : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u) :
    let v : ℝ := u
    let D : ℝ := (v ^ 26 + 1) * ((q : ℝ) * v ^ 16) ^ (40 * u ^ 8)
    let M := 9 * v ^ 10 * (1 + 10 * log v) + 4 * v ^ 8 + 34
    1 ≤ D ∧ 1 ≤ M ∧
      log D ≤ v ^ 8 * (log 2 + 40 * log (q : ℝ) + 666 * log v) ∧
      ∀ R : ℝ, 0 ≤ R → M + R ≤ v ^ 10 * (47 + R + 90 * log v) := by
  intro v D M
  have hv : 1 ≤ v := by
    change (1 : ℝ) ≤ (u : ℝ)
    exact_mod_cast hu
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hq)
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hqR
  have hlogv : 0 ≤ log v := log_nonneg hv
  have hbase : 1 ≤ (q : ℝ) * v ^ 16 := one_le_mul_of_one_le_of_one_le hqR (one_le_pow₀ hv)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by nlinarith only [one_le_pow₀ hv (n := 26)]) (one_le_pow₀ hbase)
  have hM : 1 ≤ M := by
    have hp : 0 ≤ 9 * v ^ 10 * (1 + 10 * log v) := by positivity
    have hp8 : 0 ≤ v ^ 8 := by positivity
    dsimp only [M]
    linarith only [hp, hp8]
  refine ⟨hD, hM, ?_, ?_⟩
  · have hfirst : log (v ^ 26 + 1) ≤ log 2 + 26 * log v := by
      calc
        log (v ^ 26 + 1) ≤ log (2 * v ^ 26) :=
          log_le_log (by positivity) (by nlinarith only [one_le_pow₀ hv (n := 26)])
        _ = log 2 + 26 * log v := by
          rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hv0.ne'), log_pow]
          norm_num
    have hlogD : log D = log (v ^ 26 + 1) +
        40 * v ^ 8 * (log (q : ℝ) + 16 * log v) := by
      dsimp only [D]
      rw [log_mul (by positivity) (by positivity), log_pow,
        log_mul hq0.ne' (pow_ne_zero _ hv0.ne'), log_pow]
      dsimp only [v]
      push_cast
      ring
    rw [hlogD]
    have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
    have hextend := mul_le_mul_of_nonneg_right (one_le_pow₀ hv (n := 8))
      (by positivity : 0 ≤ log 2 + 26 * log v)
    nlinarith only [hfirst, hextend]
  · intro R hR
    have hp : v ^ 8 ≤ v ^ 10 := pow_le_pow_right₀ hv (by decide)
    have hconstant := mul_le_mul_of_nonneg_right (one_le_pow₀ hv (n := 10))
      (by positivity : 0 ≤ 34 + R)
    dsimp only [M]
    nlinarith only [hp, hconstant]

/-- Real lower bound on the natural scale for all three soft-family error budgets. -/
noncomputable def softFamilyThreshold (q : ℕ) (g : ℝ) (a b c : ℕ) : ℝ :=
  let A := ((a : ℝ) + 12) * (log 2 + 40 * log (q : ℝ)) + (200 + g + |log (g / 2000000)|)
  let B := ((a : ℝ) + 12) * 666 + 12 * ((b : ℝ) + c)
  max (((|52 + g| + 2 * |90|) / 1) ^ 2)
    (max (((|A| + 2 * |B|) / (1 / 64)) ^ 2)
      (max (exp 1) (max (156 + 2 * g) (max (g / 40 + 24) (1 / g)))))

/-- At gap `w²/2` and budgets `(24,10,10)`, the sufficient threshold grows at
most quartically in inverse width. The constant is deliberately coarse. -/
theorem softFamilyThreshold_half_sq_le (q : ℕ) (hq : 2 ≤ q) {w : ℝ}
    (hw : 0 < w) (hw' : w ≤ 1) :
    softFamilyThreshold q (w ^ 2 / 2) 24 10 10 ≤
      (64 * (5000000 + 1440 * (q : ℝ))) ^ 2 * (1 + w⁻¹) ^ 4 := by
  let z := (1 + w⁻¹) ^ 2
  let K := 64 * (5000000 + 1440 * (q : ℝ))
  have hz : 1 ≤ z := one_le_pow₀ (by linarith only [inv_pos.mpr hw])
  have hg : w ^ 2 / 2 ≤ 1 := by nlinarith only [mul_nonneg hw.le (sub_nonneg.mpr hw'), hw']
  have hlog : |log (w ^ 2 / 2 / 2000000)| ≤ 4000000 * z := by
    rw [abs_of_nonpos (log_nonpos (by positivity) (by linarith only [hg]))]
    rw [← log_inv]
    have hi : (w ^ 2 / 2 / 2000000)⁻¹ = 4000000 * (w⁻¹)^2 := by
      field_simp
      ring
    rw [hi]
    have hl := log_le_sub_one_of_pos (by positivity : 0 < 4000000 * (w⁻¹)^2)
    dsimp [z]
    nlinarith only [hl, inv_pos.mpr hw]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hA := log_le_sub_one_of_pos (zero_lt_one.trans_le hq1)
  have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hK : 1000000 ≤ K := by dsimp [K]; linarith only [Nat.cast_nonneg (α := ℝ) q]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hKz : K ≤ K * z := le_mul_of_one_le_right hK0 hz
  have hlarge : 1000000 * z ≤ (K * z)^2 := by
    have h := mul_le_mul_of_nonneg_right hK (by linarith only [hz] : 0 ≤ z)
    nlinarith only [h, hKz, hK, mul_nonneg (show 0 ≤ K*z by positivity)
      (show 0 ≤ K*z-1 by linarith only [hKz, hK])]
  have he : exp 1 ≤ 3 := exp_one_lt_three.le
  have hi : 1 / (w ^ 2 / 2) = 2 * (w⁻¹)^2 := by field_simp
  have hiz : 1 / (w ^ 2 / 2) ≤ 2*z := by rw [hi]; dsimp [z]; nlinarith only [inv_pos.mpr hw]
  have hsq : K^2 * (1 + w⁻¹)^4 = (K*z)^2 := by dsimp [z]; ring
  change _ ≤ K^2 * (1+w⁻¹)^4
  rw [hsq]
  unfold softFamilyThreshold
  simp only [max_le_iff]
  norm_num only [Nat.cast_ofNat]
  rw [abs_of_nonneg (by positivity : 0 ≤ 52 + w^2/2),
    abs_of_nonneg (by have := log_nonneg hq1; positivity : 0 ≤ (36:ℝ)*(log 2+40*log (q:ℝ)) +
      (200+w^2/2+|log (w^2/2/2000000)|))]
  refine ⟨?_, ?_, by linarith only [he, hlarge, hz],
    by linarith only [hg, hlarge, hz], by linarith only [hg, hlarge, hz],
    by linarith only [hiz, hlarge, hz]⟩
  · norm_num
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hg, hKz, hK]
  · apply pow_le_pow_left₀ (by positivity)
    dsimp [K]
    have hmul := mul_le_mul_of_nonneg_left hz
      (show 0 ≤ 500000 + 1440*(q:ℝ) by positivity)
    nlinarith only [hlog, hg, hA, h2, hmul, hz]

private theorem soft_family_log_budgets_of_threshold (q : ℕ) (hq : 2 ≤ q)
    (g : ℝ) (hg : 0 < g) (a b c : ℕ) :
    ∀ u : ℕ, 2 ≤ u → softFamilyThreshold q g a b c ≤ (u : ℝ) →
      let v : ℝ := u
      let D : ℝ := (v ^ 26 + 1) * ((q : ℝ) * v ^ 16) ^ (40 * u ^ 8)
      let M := 9 * v ^ 10 * (1 + 10 * log v) + 4 * v ^ 8 + 34
      2 ≤ u ∧ 1 ≤ log v ∧ 156 + 2 * g ≤ 3 * v ^ 10 ∧
        156 + 2 * g ≤ v ^ 9 ∧ g / 40 + 24 ≤ v ^ 9 ∧
        1 ≤ g * v ^ 2 ∧ 1 ≤ D ∧ 1 ≤ M ∧ M + 5 + g ≤ v ^ 12 ∧
        ((a : ℝ) + 12) * log D + ((b : ℝ) + c) * log M +
          (200 + g + |log (g / 2000000)|) ≤ v ^ 9 / 64 := by
  intro u hu hthreshold
  simp only [softFamilyThreshold, max_le_iff] at hthreshold
  obtain ⟨h₁, h₂, hlog, hcut, hcut', hgu⟩ := hthreshold
  have hx : (1 : ℝ) ≤ u := by exact_mod_cast (by omega : 1 ≤ u)
  have hMb := affine_log_le_nat_pow_of_threshold (52 + g) 90 (p := 2)
    (by decide) (by norm_num : (0 : ℝ) < 1) hx h₁
  have hbud := affine_log_le_nat_pow_of_threshold _ _ (p := 1)
    (by decide) (by norm_num : (0 : ℝ) < 1 / 64) hx h₂
  let v : ℝ := u
  let D : ℝ := (v ^ 26 + 1) * ((q : ℝ) * v ^ 16) ^ (40 * u ^ 8)
  let M := 9 * v ^ 10 * (1 + 10 * log v) + 4 * v ^ 8 + 34
  have huv : 1 ≤ v := by
    change (1 : ℝ) ≤ (u : ℝ)
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hu)
  have hv0 : 0 < v := zero_lt_one.trans_le huv
  have hlogv : 1 ≤ log v := by
    calc
      1 = log (exp 1) := (log_exp 1).symm
      _ ≤ log v := log_le_log (exp_pos 1) hlog
  have hv9 : v ≤ v ^ 9 := by
    simpa only [pow_one] using pow_le_pow_right₀ huv (by decide : 1 ≤ 9)
  have hv10 : v ≤ v ^ 10 := by
    simpa only [pow_one] using pow_le_pow_right₀ huv (by decide : 1 ≤ 10)
  have hgu' : 1 ≤ g * v := by simpa only [v, mul_comm] using (div_le_iff₀ hg).mp hgu
  have hgu2 : 1 ≤ g * v ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left huv (by positivity : 0 ≤ g * v)
    nlinarith only [hgu', hmul]
  obtain ⟨hD, hM, hlogD, hMcoarse⟩ :=
    soft_family_log_bounds hq (le_trans (by decide : 1 ≤ 2) hu)
  have hMb' : 47 + (5 + g) + 90 * log v ≤ v ^ 2 := by
    change 47 + (5 + g) + 90 * log (u : ℝ) ≤ (u : ℝ) ^ 2
    linarith only [hMb]
  have hupper : M + 5 + g ≤ v ^ 12 := by
    calc
      M + 5 + g = M + (5 + g) := by ring
      _ ≤ v ^ 10 * (47 + (5 + g) + 90 * log v) := hMcoarse (5 + g) (by positivity)
      _ ≤ v ^ 10 * v ^ 2 := mul_le_mul_of_nonneg_left hMb' (pow_nonneg hv0.le _)
      _ = v ^ 12 := by ring
  have hlogM : log M ≤ 12 * log v := by
    calc
      log M ≤ log (v ^ 12) := log_le_log (zero_lt_one.trans_le hM) (by linarith only [hupper, hg])
      _ = 12 * log v := by rw [log_pow]; norm_num
  refine ⟨hu, hlogv, ?_, hcut.trans hv9, hcut'.trans hv9, hgu2, hD, hM, hupper, ?_⟩
  · linarith only [hcut.trans hv10, pow_nonneg hv0.le 10]
  · have hcost := add_le_add
      (mul_le_mul_of_nonneg_left hlogD (by positivity : 0 ≤ (a : ℝ) + 12))
      (mul_le_mul_of_nonneg_left hlogM (by positivity : 0 ≤ (b : ℝ) + c))
    have hsmall : 0 ≤ 12 * ((b : ℝ) + c) * log v +
        (200 + g + |log (g / 2000000)|) := by positivity
    have hextend := mul_le_mul_of_nonneg_right (one_le_pow₀ huv (n := 8)) hsmall
    calc
      ((a : ℝ) + 12) * log D + ((b : ℝ) + c) * log M +
          (200 + g + |log (g / 2000000)|) ≤
        v ^ 8 * (((a : ℝ) + 12) * (log 2 + 40 * log (q : ℝ)) +
          (200 + g + |log (g / 2000000)|) +
          (((a : ℝ) + 12) * 666 + 12 * ((b : ℝ) + c)) * log v) := by
            nlinarith only [hcost, hextend]
      _ ≤ v ^ 8 * ((1 / 64) * v) :=
        mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hbud) (pow_nonneg hv0.le _)
      _ = v ^ 9 / 64 := by ring

/-- A single natural scale simultaneously controls the soft residuals and the
squared Chebyshev shrinking factor, with count and precision evaluated at the
same parameters. This is an auxiliary calibration for ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, `t:aisefficient` and
`fig:merge-prime`, lines 1262–1268, 1373–1420 and 1664–1673.

The choices depend only on the local dimension, the positive gap and the three
natural exponent budgets. No volume or target dimension occurs. The powers
of the natural scale are a new sufficient calibration; the theorem does not
assert the printed fourth-order choice or its quantitative gap dependence. -/
theorem soft_family_calibration_of_threshold (q : ℕ) (hq : 2 ≤ q)
    (g : ℝ) (hg : 0 < g) (a b c u : ℕ) (hu : 2 ≤ u)
    (hthreshold : softFamilyThreshold q g a b c ≤ u) :
      let ell := u ^ 8
      let m := u ^ 10
      let t := 3 * (m : ℝ)
      let k := u ^ 16
      let T := (u : ℝ) ^ 9
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let M := 3 * t * (1 + log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((D : ℝ) ^ a * M ^ b)
      let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
      1 ≤ ell ∧ 2 ≤ m ∧ 1 ≤ k ∧
        156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
        1 ≤ D ∧ 1 ≤ M ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < xi ∧ xi ≤ 1 ∧
        3 * (32 * exp (-(T - g / 40 - 24) / 8) + (t / m) * (T / t) ^ m) ≤
          tau * g / 1000000 ∧
        3 * (32 * exp (-(T - 156 - 2 * g) / 8) + (t / m) * (T / t) ^ m) ≤
          tau * g / 1000000 ∧
        (2 * exp (-2 * (k : ℝ) * sqrt ((g / 2) / (M + xi + 4 + g)))) ^ 2 ≤
          1 / ((D : ℝ) ^ 12 * M ^ c) := by
  obtain ⟨_, hlogu, ht, hT, hT', hgu, hD, hM, hupper, hbudget⟩ :=
    soft_family_log_budgets_of_threshold q hq g hg a b c u hu hthreshold
  intro ell m t k T D M tau xi
  have hu1 : 1 ≤ u := le_trans (by decide : 1 ≤ 2) hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have huv : 1 ≤ (u : ℝ) := by exact_mod_cast hu1
  have hdiv : u ^ 16 / u ^ 8 = u ^ 8 := by
    rw [show u ^ 16 = u ^ 8 * u ^ 8 by ring,
      Nat.mul_div_cancel_left _ (pow_pos hu0 _)]
  have hDformula : (D : ℝ) =
      ((u : ℝ) ^ 26 + 1) * ((q : ℝ) * (u : ℝ) ^ 16) ^ (40 * u ^ 8) := by
    dsimp only [D, m, k, ell]
    rw [show u ^ 10 * u ^ 16 = u ^ 26 by ring, hdiv,
      show 36 * u ^ 8 + 4 * u ^ 8 = 40 * u ^ 8 by ring]
    push_cast
    rfl
  have hMformula : M =
      9 * (u : ℝ) ^ 10 * (1 + 10 * log (u : ℝ)) + 4 * (u : ℝ) ^ 8 + 34 := by
    dsimp only [M, t, m, ell]
    push_cast
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hD1 : 1 ≤ (D : ℝ) := hDformula.symm ▸ hD
  have hM1 : 1 ≤ M := hMformula.symm ▸ hM
  have hD0 : 0 < (D : ℝ) := zero_lt_one.trans_le hD1
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  have htau : 0 < tau := by dsimp only [tau]; positivity
  have htau1 : tau ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (D : ℝ) ^ a * M ^ b)).mpr
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1) (one_le_pow₀ hM1)
  have hxi : 0 < xi := lt_min (by norm_num) (by positivity)
  have hxi1 : xi ≤ 1 := min_le_left _ _
  have hupper' : M + xi + 4 + g ≤ (u : ℝ) ^ 12 := by
    rw [← hMformula] at hupper
    linarith only [hupper, hxi1]
  have hbudget' : ((a : ℝ) + 12) * log (D : ℝ) + ((b : ℝ) + c) * log M +
      (200 + g + |log (g / 2000000)|) ≤ (u : ℝ) ^ 9 / 64 := by
    simpa only [hDformula, hMformula] using hbudget
  have hbounds := soft_family_budgets_of_log_bound huv hlogu hg hD1 hM1
    (m := m) (by simp only [m, Nat.cast_pow]) hupper' hxi hgu hbudget'
  refine ⟨one_le_pow₀ hu1, ?_, one_le_pow₀ hu1, ?_, hT, hT', ?_,
    hM1, htau, htau1, hxi, hxi1, ?_⟩
  · exact hu.trans (by
      simpa only [m, pow_one] using pow_le_pow_right₀ hu1 (by decide : 1 ≤ 10))
  · simpa only [t, m, Nat.cast_pow] using ht
  · exact_mod_cast hD1
  · simpa only [tau, t, T, k, Nat.cast_pow] using hbounds

/-- A natural scale satisfies the corrected scalar calibration for the soft estimates
of ALVV, arXiv:1602.08828v2. See `soft_family_calibration_of_threshold` for the
sufficient threshold and its relation to the paper. -/
theorem exists_soft_family_calibration (q : ℕ) (hq : 2 ≤ q)
    (g : ℝ) (hg : 0 < g) (a b c : ℕ) :
    ∃ u : ℕ, 2 ≤ u ∧
      let ell := u ^ 8
      let m := u ^ 10
      let t := 3 * (m : ℝ)
      let k := u ^ 16
      let T := (u : ℝ) ^ 9
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let M := 3 * t * (1 + log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((D : ℝ) ^ a * M ^ b)
      let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
      1 ≤ ell ∧ 2 ≤ m ∧ 1 ≤ k ∧
        156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
        1 ≤ D ∧ 1 ≤ M ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < xi ∧ xi ≤ 1 ∧
        3 * (32 * exp (-(T - g / 40 - 24) / 8) + (t / m) * (T / t) ^ m) ≤
          tau * g / 1000000 ∧
        3 * (32 * exp (-(T - 156 - 2 * g) / 8) + (t / m) * (T / t) ^ m) ≤
          tau * g / 1000000 ∧
        (2 * exp (-2 * (k : ℝ) * sqrt ((g / 2) / (M + xi + 4 + g)))) ^ 2 ≤
          1 / ((D : ℝ) ^ 12 * M ^ c) := by
  let u := max 2 ⌈softFamilyThreshold q g a b c⌉₊
  have hu : 2 ≤ u := le_max_left ..
  have h : softFamilyThreshold q g a b c ≤ (u : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  exact ⟨u, hu, soft_family_calibration_of_threshold q hq g hg a b c u hu h⟩

/-- For inverse-width estimates, a polynomially bounded natural scale meets the
threshold of `soft_family_calibration_of_threshold` for the budgets `(24,10,10)`. -/
theorem exists_soft_family_scale_half_sq (q : ℕ) (hq : 2 ≤ q) {w : ℝ}
    (hw : 0 < w) (hw' : w ≤ 1) :
    ∃ u : ℕ, 2 ≤ u ∧ softFamilyThreshold q (w^2 / 2) 24 10 10 ≤ u ∧
      (u : ℝ) ≤ ((64 * (5000000 + 1440 * (q : ℝ))) ^ 2 + 2) * (1 + w⁻¹) ^ 4 := by
  let K := 64 * (5000000 + 1440 * (q : ℝ))
  let z := (1 + w⁻¹) ^ 4
  have hz : 1 ≤ z := one_le_pow₀ (by linarith only [inv_pos.mpr hw])
  let u := max 2 ⌈K^2*z⌉₊
  refine ⟨u, le_max_left .., (softFamilyThreshold_half_sq_le q hq hw hw').trans
    ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))), ?_⟩
  change (↑(max 2 ⌈K^2*z⌉₊) : ℝ) ≤ (K^2 + 2)*z
  rw [Nat.cast_max, max_le_iff]
  have hpos : 0 ≤ K^2*z := mul_nonneg (sq_nonneg _) (by linarith only [hz])
  constructor
  · norm_num
    nlinarith only [hpos, hz]
  · nlinarith only [Nat.ceil_lt_add_one hpos, hz]

end Real
