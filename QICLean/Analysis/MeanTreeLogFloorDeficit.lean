/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeLogFloorExp

/-!
# A uniform error for the logarithmic lower comparison

For exponents of the form `κ Lⱼ - r`, the loss from a mass deficit in
`[0,1]` has a remainder independent of both that deficit and the terminal
probabilities. In the area-law comparison `κ` is proportional to the copy
number, while `r` and the logarithm of the positive floor are sublinear.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 615–640,
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace Matrix.MeanTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The error in the logarithmic mass estimate is independent of the tree
and of every deficit between zero and one. Source: `07-comparators.tex`,
lines 615–640, `comparator:tree-log-lower`. -/
theorem weighted_log_floor_deficit_lower (T : MeanTree ι)
    {b : ℝ} (hb : 0 < b) {κ : ℝ} (hκ : 0 ≤ κ)
    (L : ι → ℝ) {U : ℝ} (hU : ∀ j, L j ≤ U) (r : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) :
    let ell := ∑ j, T.weight j * Real.log (b + Real.exp (κ * L j - r) / 2)
    κ * ((∑ j, T.weight j * L j) - δ * max 0 U) -
        (2 * |r| + |Real.log b| + Real.log 2 + Real.log (3 / 2)) ≤
      ell - δ * (ell - Real.log b) := by
  intro ell
  obtain ⟨hlower, _, hupper⟩ := T.weighted_log_add_half_exp_bounds hb
    (fun j ↦ κ * L j - r)
    (fun j ↦ sub_le_sub_right (mul_le_mul_of_nonneg_left (hU j) hκ) r)
  have hsum : (∑ j, T.weight j * (κ * L j - r)) =
      κ * (∑ j, T.weight j * L j) - r := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [T.sum_weight, one_mul]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hsum] at hlower
  have hmax : max 0 (κ * U - r - Real.log b) ≤
      κ * max 0 U + |r| + |Real.log b| := by
    apply max_le
    · positivity
    · have hmain := mul_le_mul_of_nonneg_left (le_max_right 0 U) hκ
      have hr := neg_le_abs r
      have hb' := neg_le_abs (Real.log b)
      linarith only [hmain, hr, hb']
  have hupper' := hupper.trans (add_le_add_left hmax (Real.log (3 / 2)))
  have hlog : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have herror : 0 ≤ |r| + |Real.log b| + Real.log (3 / 2) := by positivity
  have hdeficit := mul_le_mul_of_nonneg_left hupper' hδ
  have hsmall := mul_le_mul_of_nonneg_right hδone herror
  have hr := le_abs_self r
  dsimp only [ell] at hlower hdeficit ⊢
  nlinarith only [hlower, hdeficit, hsmall, hr]

end Matrix.MeanTree
