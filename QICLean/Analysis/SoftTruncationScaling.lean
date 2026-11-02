/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncation

/-!
# Independent scale and order for the soft-truncation remainder

An exact scaling identity transfers the existing equal-scale exponential remainder to independent
parameters. This supports a compatible small heat-time choice in ALVV, arXiv:1602.08828v2,
`def:ft` and `lem:exp-approx-eff`, lines 1152–1173 and 1262–1268. It does not assert the printed
uniform energy estimate; see
https://sirui-lu.com/TNLean/paper-gaps/alvv16_soft_truncation_energy_estimate.pdf.
-/

namespace Real

/-- Changing the soft-truncation scale rescales its input and output exactly. Supporting ALVV,
arXiv:1602.08828v2, `def:ft`, lines 1152–1157. -/
theorem softTruncation_scale (t s : ℝ) (m : ℕ) (x : ℝ) (hs : s ≠ 0) :
    softTruncation t m x = (t / s) * softTruncation s m ((s / t) * x) := by
  have he : ((s / t) * x) / s = x / t := by field_simp
  simp only [softTruncation, he]
  field_simp

/-- For an independent positive scale at most four times the order, the same exponential
weight controls the soft remainder. Supporting a compatible heat-time regime for ALVV,
arXiv:1602.08828v2, `def:ft` and `lem:exp-approx-eff`, lines 1152–1173 and 1262–1268. -/
theorem softTruncation_remainder_le_exp_of_scale_le (m : ℕ) (hm : 0 < m)
    (t x : ℝ) (ht : 0 < t) (htm : t ≤ 4 * m) (hx : 0 ≤ x) :
    x - softTruncation t m x ≤ 16 * exp (x / 8 - t / 16) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let theta := t / (8 * (m : ℝ))
  have htheta : 0 < theta := div_pos ht (by positivity)
  have hhalf : theta ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have he := softTruncation_remainder_le_exp m hm theta ((m : ℝ) / t * x)
    htheta hhalf (mul_nonneg (div_nonneg hmR.le ht.le) hx)
  have hscale : x - softTruncation t m x =
      (t / (m : ℝ)) * ((m : ℝ) / t * x -
        softTruncation (m : ℝ) m ((m : ℝ) / t * x)) := by
    rw [softTruncation_scale t (m : ℝ) m x hmR.ne']
    field_simp
  rw [hscale]
  refine (mul_le_mul_of_nonneg_left he (div_nonneg ht.le hmR.le)).trans_eq ?_
  have hexp : theta * ((m : ℝ) / t * x) - theta * m / 2 = x / 8 - t / 16 := by
    dsimp only [theta]
    field_simp
    ring
  rw [hexp, ← mul_assoc]
  congr 1
  dsimp only [theta]
  field_simp
  ring

end Real
