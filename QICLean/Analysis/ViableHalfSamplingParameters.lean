/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical margins for half-dimensional resampling and trimming

The overlap supplied by a half-dimensional Haar sample makes one error
reduction substantially stronger than the usual bootstrap threshold.
Transferring to the original target then leaves a fixed margin for actual
collective trimming relative to a nearby reference.

These scalar auxiliaries support ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-dg`, lines 1065–1074, and the collective
trimming argument, lines 1801–1813.
**Local fix (bootstrap and trimming constants):** the numerical margins
retain the corrected constants recorded in
`docs/paper-gaps/alvv16_bootstrap_constants.tex` and
`docs/paper-gaps/alvv16_trimming_constant.tex`.
-/

namespace Real

/-- The half-sample overlap leaves a reduced-target error at most one
part in ten thousand. This refines the numerical step in ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-dg`, lines 1065–1074. -/
theorem half_sampling_filter_error_le {d Delta alpha : ℝ}
    (hd : 2 ≤ d) (hDelta : d ^ 12 * Delta ≤ 1 / 100000)
    (halpha : (3 / 100) / d ^ 2 ≤ alpha) :
    Delta / alpha ^ 2 ≤ 1 / 10000 := by
  have hd0 : 0 < d := by linarith only [hd]
  have ha0 : 0 < alpha :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (3 / 100) / d ^ 2) halpha
  have hprod : (3 / 100 : ℝ) ≤ alpha * d ^ 2 :=
    (div_le_iff₀ (pow_pos hd0 2)).mp halpha
  have hsq : (9 / 10000 : ℝ) ≤ alpha ^ 2 * d ^ 4 := by
    nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 100) hprod 2]
  have hd8 : (256 : ℝ) ≤ d ^ 8 := by
    calc
      (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ d ^ 8 := pow_le_pow_left₀ (by norm_num) hd 8
  have hlarge : (144 / 625 : ℝ) ≤ alpha ^ 2 * d ^ 12 := by
    calc
      (144 / 625 : ℝ) = (9 / 10000) * 256 := by norm_num
      _ ≤ (9 / 10000) * d ^ 8 := mul_le_mul_of_nonneg_left hd8 (by norm_num)
      _ ≤ (alpha ^ 2 * d ^ 4) * d ^ 8 :=
        mul_le_mul_of_nonneg_right hsq (pow_nonneg hd0.le 8)
      _ = alpha ^ 2 * d ^ 12 := by ring
  apply (div_le_iff₀ (pow_pos ha0 2)).mpr
  exact (mul_le_mul_iff_left₀ (pow_pos hd0 12)).mp (by nlinarith only [hDelta, hlarge])

/-- A weakly viable sample for the fixed original target remains viable
for every sufficiently close improving target, with at least half its
success parameter. This weighted transfer supports ALVV,
arXiv:1602.08828v2, Lemma `l:close` and the bootstrap at lines 1065–1074. -/
theorem half_sampling_transfer_error_le {alpha epsilon : ℝ}
    (halpha : 0 < alpha) (hepsilon : epsilon ≤ alpha ^ 2 / 100) :
    (1 + alpha / 4) * (1 - alpha) + (1 + 1 / (alpha / 4)) * epsilon ≤
      1 - alpha / 2 := by
  have hc : 0 ≤ 1 + 1 / (alpha / 4) := by positivity
  calc
    _ ≤ (1 + alpha / 4) * (1 - alpha) +
        (1 + 1 / (alpha / 4)) * (alpha ^ 2 / 100) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hepsilon hc)
    _ = 1 - (71 / 100) * alpha - (6 / 25) * alpha ^ 2 := by
      field_simp [ne_of_gt halpha]
      ring
    _ ≤ 1 - alpha / 2 := by nlinarith only [halpha, sq_nonneg alpha]

/-- A reference accuracy and a trimming threshold fit the fixed margin
left after one half-dimensional sample and transfer to the original target.
Supporting ALVV, arXiv:1602.08828v2, the collective trimming argument,
lines 1801–1813, with its corrected increment. -/
theorem half_sampling_trim_error_le {delta epsilon z : ℝ}
    (hdelta : delta ≤ 27 / 2500) (hepsilon : epsilon ≤ 1 / 100000)
    (hz : z ≤ 1 / 1000) :
    (1 + (1 / 20 : ℝ)) * ((1 + (1 / 20 : ℝ)) * delta +
      (1 + 1 / (1 / 20 : ℝ)) * epsilon + 2 * z) +
      (1 + 1 / (1 / 20 : ℝ)) * epsilon ≤ 3 / 200 := by
  norm_num at *
  linarith only [hdelta, hepsilon, hz]

end Real
