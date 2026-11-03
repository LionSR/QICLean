/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReferencePolynomialBound

/-!
# Polynomial control of the length-dependent interleaved count

The calibrated interleaved construction contains a scale
\(U+\log(1+w)\), where \(w\) is logarithmic in length and ground-space rank.
Its seventh power and the product of its fourth power with \(\sqrt w\)
are bounded by a constant times \(w\). This converts the honest filter
count estimate into polynomial growth at fixed physical parameters.
These are scalar auxiliaries for ALVV, arXiv:1602.08828v2,
Theorem `t:alg1`, lines 1777–1817, with the corrected interleaved parameters.
No printed parameter profile or computational running time is asserted.
-/

namespace Real

/-- A fixed affine logarithmic scale is bounded by a small positive power.
Scalar auxiliary to the calibrated ALVV interleaved construction,
arXiv:1602.08828v2, lines 1797–1805. -/
theorem log_linear_scale_le_sixteenth_power {U w : ℝ}
    (hU : 1 ≤ U) (hw : 1 ≤ w) :
    U + log (1 + w) ≤ (U + 17) * w ^ (1 / 16 : ℝ) := by
  have hlog : log (1 + w) ≤ 1 + 16 * w ^ (1 / 16 : ℝ) := by
    have hpower := log_le_rpow_div (by linarith : 0 ≤ w)
      (by norm_num : (0 : ℝ) < 1 / 16)
    have htwo : log (2 : ℝ) ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
        log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    calc
      log (1 + w) ≤ log (2 * w) := log_le_log (by linarith) (by linarith)
      _ = log 2 + log w := log_mul (by norm_num) (by linarith)
      _ ≤ 1 + 16 * w ^ (1 / 16 : ℝ) := by linarith
  have hroot : 1 ≤ w ^ (1 / 16 : ℝ) := by
    simpa only [rpow_zero] using
      rpow_le_rpow_of_exponent_le hw (by norm_num : (0 : ℝ) ≤ 1 / 16)
  nlinarith only [hlog,
    mul_nonneg (by linarith only [hU] : 0 ≤ U + 1) (sub_nonneg.mpr hroot)]

/-- The two logarithmic terms in the actual interleaved count bound are
at most linear in the chain-size logarithm. Scalar auxiliary to ALVV,
arXiv:1602.08828v2, lines 1797–1817, for the calibrated length-dependent count. -/
theorem interleaved_log_powers_le_linear {U w : ℝ}
    (hU : 1 ≤ U) (hw : 1 ≤ w) :
    (U + log (1 + w)) ^ 7 ≤ (U + 17) ^ 7 * w ∧
      sqrt w * (U + log (1 + w)) ^ 4 ≤ (U + 17) ^ 4 * w := by
  have hbase := log_linear_scale_le_sixteenth_power hU hw
  have hv0 : 0 ≤ U + log (1 + w) :=
    add_nonneg (by linarith only [hU]) (log_nonneg (by linarith only [hw]))
  constructor
  · calc
      (U + log (1 + w)) ^ 7 ≤ ((U + 17) * w ^ (1 / 16 : ℝ)) ^ 7 :=
        pow_le_pow_left₀ hv0 hbase 7
      _ = (U + 17) ^ 7 * w ^ (7 / 16 : ℝ) := by
        rw [mul_pow, ← rpow_mul_natCast (by linarith only [hw] : 0 ≤ w)]
        norm_num
      _ ≤ (U + 17) ^ 7 * w := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [rpow_one] using
          rpow_le_rpow_of_exponent_le hw (by norm_num : (7 / 16 : ℝ) ≤ 1)
  · calc
      sqrt w * (U + log (1 + w)) ^ 4 ≤
          sqrt w * ((U + 17) * w ^ (1 / 16 : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hbase 4) (sqrt_nonneg w)
      _ = (U + 17) ^ 4 * w ^ (3 / 4 : ℝ) := by
        rw [mul_pow, ← rpow_mul_natCast (by linarith only [hw] : 0 ≤ w)]
        norm_num
        rw [sqrt_eq_rpow, mul_left_comm, ← rpow_add (by linarith only [hw] : 0 < w)]
        norm_num
      _ ≤ (U + 17) ^ 4 * w := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [rpow_one] using
          rpow_le_rpow_of_exponent_le hw (by norm_num : (3 / 4 : ℝ) ≤ 1)

end Real
