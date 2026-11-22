/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical bounds for sampling between nested low-energy targets

These scalar estimates support ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. They discharge numerical conditions
for the corrected half-size sample; they do not choose physical targets
or assert the low-density induction.

**Local fix (complex sphere net count):** The failure expression retains
the exponent twice the complex target dimension, as documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

namespace Real

/-- At a sufficiently large logarithmic count scale, the corrected
complex-sphere sampling failure is strictly below one. The sample lower
bound and logarithmic dimension comparison are explicit scalar premises.
Supporting ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. -/
theorem nested_sampling_failure_lt_one {D r s Q alpha : ℝ} {t : ℕ}
    (hD : 1 ≤ D) (hlogD : 100 ≤ log D) (hr : 1 ≤ r)
    (ht : (t : ℝ) ≤ r) (hQ : 0 < Q)
    (hlogQ : log Q ≤ log r + (13 / 2) * log D)
    (hs : r * D / 4 < s) (halpha : 1 / (36 * D ^ 6) ≤ alpha) :
    (1 + 2 / sqrt alpha) ^ (2 * t) * Q * exp (-(s / 16)) < 1 := by
  have hD0 : 0 < D := by linarith only [hD]
  have hr0 : 0 < r := by linarith only [hr]
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by positivity) halpha
  have hroot : 0 < sqrt alpha := sqrt_pos.mpr halpha0
  have hD3 : 1 ≤ D ^ 3 := one_le_pow₀ hD
  have hrootLower : 1 / (6 * D ^ 3) ≤ sqrt alpha := by
    apply le_sqrt_of_sq_le
    calc
      (1 / (6 * D ^ 3)) ^ 2 = 1 / (36 * D ^ 6) := by ring
      _ ≤ alpha := halpha
  have hrootMul : 1 ≤ sqrt alpha * (6 * D ^ 3) :=
    (div_le_iff₀ (by positivity : 0 < 6 * D ^ 3)).mp hrootLower
  have hratio : 2 / sqrt alpha ≤ 12 * D ^ 3 := by
    apply (div_le_iff₀ hroot).mpr
    nlinarith only [hrootMul]
  let base := 1 + 2 / sqrt alpha
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hbase1 : 1 ≤ base := by
    dsimp only [base]
    exact le_add_of_nonneg_right (by positivity)
  have hbaseBound : base ≤ 13 * D ^ 3 := by
    dsimp only [base]
    linarith only [hratio, hD3]
  have hlogBase : log base ≤ log 13 + 3 * log D := by
    have hb := log_le_log hbase hbaseBound
    simpa only [log_mul (by norm_num : (13 : ℝ) ≠ 0) (pow_ne_zero 3 hD0.ne'),
      log_pow, Nat.cast_ofNat] using hb
  have hlogBase0 : 0 ≤ log base := log_nonneg hbase1
  have hlog13 : log (13 : ℝ) ≤ 12 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13)]
  have hlogr : log r ≤ r :=
    (log_le_sub_one_of_pos hr0).trans (by linarith)
  have hnet : (2 * (t : ℝ)) * log base + log Q ≤ 13 * r * log D := by
    have hb := mul_le_mul_of_nonneg_left hlogBase (by positivity : 0 ≤ 2 * r)
    have ht' := mul_le_mul_of_nonneg_right ht hlogBase0
    have hc := mul_le_mul_of_nonneg_left hlog13 hr0.le
    have hscale := mul_le_mul_of_nonneg_right hr
      (show 0 ≤ log D by linarith only [hlogD])
    have hlarge := mul_le_mul_of_nonneg_left hlogD hr0.le
    nlinarith only [hb, ht', hc, hscale, hlarge, hlogQ, hlogr]
  have hDlarge : 832 * log D < D := by
    have hx : 0 ≤ log D := by linarith only [hlogD]
    have hcube := pow_div_factorial_le_exp (log D) hx 3
    norm_num only [Nat.factorial, Nat.cast_ofNat] at hcube
    rw [exp_log hD0] at hcube
    have hsquare : 10000 ≤ (log D) ^ 2 := by nlinarith only [hlogD]
    have hcubic := mul_le_mul_of_nonneg_right hsquare hx
    nlinarith only [hcube, hcubic, hlogD]
  have hnegative : 13 * r * log D - s / 16 < 0 := by
    have hb := mul_lt_mul_of_pos_left hDlarge hr0
    nlinarith only [hb, hs]
  have hproduct : 0 < base ^ (2 * t) * Q * exp (-(s / 16)) := by positivity
  have hlogFailure : log (base ^ (2 * t) * Q * exp (-(s / 16))) < 0 := by
    rw [log_mul (mul_pos (pow_pos hbase _) hQ).ne' (exp_ne_zero _),
      log_mul (pow_ne_zero _ hbase.ne') hQ.ne', log_pow, log_exp]
    push_cast
    linarith only [hnet, hnegative]
  have hb := exp_lt_exp.mpr hlogFailure
  rwa [exp_log hproduct, exp_zero] at hb

/-- The calibrated twelfth-power suppression controls the lower-target
sampling error once the squared sampling fraction has its dyadic lower
bound. Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem nested_sampling_error_le {D Delta alpha : ℝ} (hD : 8 ≤ D)
    (htrade : D ^ 12 * Delta ≤ 1 / 100000)
    (halpha : 9 / (10000 * D ^ 11) ≤ alpha ^ 2) :
    Delta / alpha ^ 2 ≤ 1 / 400 := by
  have hD0 : 0 < D := by linarith only [hD]
  have ha : 0 < alpha ^ 2 := lt_of_lt_of_le (by positivity) halpha
  have hdelta : Delta ≤ 1 / (100000 * D ^ 12) := by
    apply (le_div_iff₀ (by positivity : 0 < 100000 * D ^ 12)).mpr
    nlinarith only [htrade]
  have hscale := mul_le_mul_of_nonneg_right hD (pow_nonneg hD0.le 11)
  have hbound : 1 / (100000 * D ^ 12) ≤
      (1 / 400) * (9 / (10000 * D ^ 11)) := by
    calc
      1 / (100000 * D ^ 12) ≤ 9 / (4000000 * D ^ 11) :=
        (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by
          nlinarith only [hscale, pow_nonneg hD0.le 11])
      _ = (1 / 400) * (9 / (10000 * D ^ 11)) := by ring
  apply (div_le_iff₀ ha).mpr
  exact hdelta.trans (hbound.trans
    (mul_le_mul_of_nonneg_left halpha (by norm_num)))

/-- A logarithmic comparison of the two actual counts implies the
squared dimension ratio needed in the low-density sampling step. This
uses integer powers only. Auxiliary to ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem nested_sampling_count_comparison {D Dnext r p Q : ℝ}
    (hD : 0 < D) (hnext : 0 < Dnext) (hr : 0 < r) (hQ : 0 < Q)
    (hcount : log Dnext ≤ (13 / 6) * log D)
    (hp : r * D ^ 3 < p) (hupper : Q ≤ r * Dnext ^ 3) :
    log Q ≤ log r + (13 / 2) * log D ∧ Q ^ 2 ≤ p ^ 2 * D ^ 7 := by
  have hcountPower : Dnext ^ 6 ≤ D ^ 13 := by
    apply (log_le_log_iff (pow_pos hnext 6) (pow_pos hD 13)).mp
    simp only [log_pow, Nat.cast_ofNat]
    linarith only [hcount]
  constructor
  · have hb := log_le_log hQ hupper
    rw [log_mul hr.ne' (pow_ne_zero 3 hnext.ne'), log_pow] at hb
    norm_num only [Nat.cast_ofNat] at hb
    linarith only [hb, hcount]
  · have hQsquare := pow_le_pow_left₀ hQ.le hupper 2
    have hpSquare := pow_le_pow_left₀ (by positivity : 0 ≤ r * D ^ 3) hp.le 2
    calc
      Q ^ 2 ≤ (r * Dnext ^ 3) ^ 2 := hQsquare
      _ = r ^ 2 * Dnext ^ 6 := by ring
      _ ≤ r ^ 2 * D ^ 13 := mul_le_mul_of_nonneg_left hcountPower (sq_nonneg r)
      _ = (r * D ^ 3) ^ 2 * D ^ 7 := by ring
      _ ≤ p ^ 2 * D ^ 7 := mul_le_mul_of_nonneg_right hpSquare (pow_nonneg hD.le 7)

/-- The squared dimension comparison and the integer-quotient lower
bound imply both sampling-fraction estimates used above. Auxiliary to
ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128.
The sample dimension enters as a real variable here; its natural quotient
and the physical count comparison are separate inputs to this lemma. -/
theorem nested_sampling_fraction_bounds {D p Q s : ℝ} (hD : 1 ≤ D)
    (hp : 0 < p) (hQ : 0 < Q) (hs : 0 < s)
    (hps : p ≤ 4 * D ^ 2 * s) (hQp : Q ^ 2 ≤ p ^ 2 * D ^ 7) :
    let alpha := 3 * s / (25 * Q)
    1 / (36 * D ^ 6) ≤ alpha ∧ 9 / (10000 * D ^ 11) ≤ alpha ^ 2 := by
  intro alpha
  have hD0 : 0 < D := by linarith only [hD]
  have hpSquare : p ^ 2 ≤ (4 * D ^ 2 * s) ^ 2 :=
    pow_le_pow_left₀ hp.le hps 2
  have hQsquare : Q ^ 2 ≤ 16 * D ^ 11 * s ^ 2 := by
    calc
      Q ^ 2 ≤ p ^ 2 * D ^ 7 := hQp
      _ ≤ (4 * D ^ 2 * s) ^ 2 * D ^ 7 :=
        mul_le_mul_of_nonneg_right hpSquare (pow_nonneg hD0.le 7)
      _ = 16 * D ^ 11 * s ^ 2 := by ring
  have hDpower : D ^ 7 ≤ D ^ 8 := by
    have hb := mul_le_mul_of_nonneg_right hD (pow_nonneg hD0.le 7)
    nlinarith only [hb]
  have hlinear : Q ≤ p * D ^ 4 := by
    have hbound : Q ^ 2 ≤ (p * D ^ 4) ^ 2 := by
      calc
        Q ^ 2 ≤ p ^ 2 * D ^ 7 := hQp
        _ ≤ p ^ 2 * D ^ 8 := mul_le_mul_of_nonneg_left hDpower (sq_nonneg p)
        _ = (p * D ^ 4) ^ 2 := by ring
    nlinarith only [hbound, hQ, mul_pos hp (pow_pos hD0 4)]
  have hQbound : Q ≤ 4 * D ^ 6 * s := by
    calc
      Q ≤ p * D ^ 4 := hlinear
      _ ≤ (4 * D ^ 2 * s) * D ^ 4 :=
        mul_le_mul_of_nonneg_right hps (pow_nonneg hD0.le 4)
      _ = 4 * D ^ 6 * s := by ring
  constructor
  · change 1 / (36 * D ^ 6) ≤ 3 * s / (25 * Q)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hQbound, mul_nonneg (pow_nonneg hD0.le 6) hs.le]
  · change 9 / (10000 * D ^ 11) ≤ (3 * s / (25 * Q)) ^ 2
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hQsquare]

/-- The count growth and half-size sample bounds jointly discharge both
numerical premises of the nested-target sampling theorem. The original
physical dimension and the target subspaces do not enter this scalar
statement. Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem nested_sampling_conditions {D Dnext r p Q s Delta : ℝ} {t : ℕ}
    (hD : 8 ≤ D) (hlogD : 100 ≤ log D) (hnext : 0 < Dnext)
    (hr : 1 ≤ r) (ht : (t : ℝ) ≤ r) (hQ : 0 < Q) (hs : 0 < s)
    (hcount : log Dnext ≤ (13 / 6) * log D)
    (hp : r * D ^ 3 < p) (hupper : Q ≤ r * Dnext ^ 3)
    (hps : p ≤ 4 * D ^ 2 * s) (htrade : D ^ 12 * Delta ≤ 1 / 100000) :
    let alpha := 3 * s / (25 * Q)
    (1 + 2 / sqrt alpha) ^ (2 * t) * Q * exp (-(s / 16)) < 1 ∧
      Delta / alpha ^ 2 ≤ 1 / 400 := by
  intro alpha
  have hD0 : 0 < D := by linarith only [hD]
  have hr0 : 0 < r := by linarith only [hr]
  have hp0 : 0 < p := lt_trans (by positivity) hp
  obtain ⟨hlogQ, hQsquare⟩ :=
    nested_sampling_count_comparison hD0 hnext hr0 hQ hcount hp hupper
  obtain ⟨halpha, halphaSquare⟩ :=
    nested_sampling_fraction_bounds (by linarith only [hD]) hp0 hQ hs hps hQsquare
  have hsLower : r * D / 4 < s := by
    apply (mul_lt_mul_iff_of_pos_left (by positivity : 0 < 4 * D ^ 2)).mp
    calc
      (4 * D ^ 2) * (r * D / 4) = r * D ^ 3 := by ring
      _ < p := hp
      _ ≤ 4 * D ^ 2 * s := hps
  exact ⟨nested_sampling_failure_lt_one (by linarith only [hD]) hlogD hr ht hQ
    hlogQ hsLower halpha, nested_sampling_error_le hD htrade halphaSquare⟩

end Real
