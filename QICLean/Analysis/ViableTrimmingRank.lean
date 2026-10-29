/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableTrimmingRadius

/-!
# The integer rank bound at the common trimming radius

The uniform radius retains the genuine squared reference bond. Its
weighted Schmidt-rank conclusion gives an explicit integer rank bound.
This supports ALVV, arXiv:1602.08828v2, collective trimming,
lines 660–697, and the degenerate-ground-space analysis,
lines 1801–1805; the numerical radius here is an auxiliary choice.
-/

namespace Real

/-- Convert the weighted trimming estimate at the chosen common radius
into an explicit integer rank bound. Supporting ALVV,
arXiv:1602.08828v2, collective trimming, lines 662–663 and 690–692. -/
theorem viable_node_trimming_rank_bound {L D count rank : ℕ} (hD : 1 ≤ D)
    (hbound : (1 / (1000 * (D : ℝ) * sqrt ((L : ℝ) + 1))) ^ 2 * rank ≤ count) :
    rank ≤ 1000000 * D ^ 2 * (L + 1) * count := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hden : 0 < (1000000 : ℝ) * (D : ℝ) ^ 2 * ((L : ℝ) + 1) := by positivity
  have hxi : (1 / (1000 * (D : ℝ) * sqrt ((L : ℝ) + 1))) ^ 2 =
      1 / ((1000000 : ℝ) * (D : ℝ) ^ 2 * ((L : ℝ) + 1)) := by
    simp only [div_pow, mul_pow, one_pow, sq_sqrt (by positivity : 0 ≤ (L : ℝ) + 1)]
    norm_num
  have hquot : (rank : ℝ) / ((1000000 : ℝ) * (D : ℝ) ^ 2 * ((L : ℝ) + 1)) ≤ count := by
    simpa only [hxi, one_div_mul_eq_div] using hbound
  have hrank := (div_le_iff₀ hden).mp hquot
  have hrankR : (rank : ℝ) ≤ (1000000 : ℝ) * (D : ℝ) ^ 2 * ((L : ℝ) + 1) * count := by
    nlinarith only [hrank]
  exact_mod_cast hrankR

end Real
