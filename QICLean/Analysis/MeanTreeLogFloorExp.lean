/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.FiniteTree

/-!
# Logarithmic estimates after adding a positive floor

The scalar comparison `b + exp(L)/2` is bounded above and below on the
logarithmic scale with explicit constant errors. Averaging these estimates
with the terminal weights of a mean tree preserves the constants,
independently of the tree and its probabilities.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 615–629, preceding
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace Real

/-- Adding a nonnegative floor changes the logarithmic lower bound by at
most `log 2`. Source: `07-comparators.tex`, lines 615–629. -/
theorem sub_log_two_le_log_add_half_exp {b : ℝ} (hb : 0 ≤ b) (L : ℝ) :
    L - log 2 ≤ log (b + exp L / 2) := by
  have h := log_le_log (half_pos (exp_pos L))
    (le_add_of_nonneg_left hb : exp L / 2 ≤ b + exp L / 2)
  simpa only [log_div (exp_ne_zero L) (by norm_num : (2 : ℝ) ≠ 0), log_exp] using h

/-- The logarithm above the floor is at most the positive part of the
relative exponent, with the explicit error `log (3/2)`.
Source: `07-comparators.tex`, lines 615–629. -/
theorem log_add_half_exp_sub_log_le {b : ℝ} (hb : 0 < b) (L : ℝ) :
    log (b + exp L / 2) - log b ≤ max 0 (L - log b) + log (3 / 2) := by
  have hbmax : b ≤ exp (max (log b) L) := by
    simpa only [exp_log hb] using exp_le_exp.mpr (le_max_left (log b) L)
  have hLmax : exp L ≤ exp (max (log b) L) :=
    exp_le_exp.mpr (le_max_right (log b) L)
  have hsum : b + exp L / 2 ≤ (3 / 2) * exp (max (log b) L) := by
    linarith only [hbmax, hLmax]
  have hlog := log_le_log (add_pos hb (half_pos (exp_pos L))) hsum
  rw [log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (exp_ne_zero _), log_exp] at hlog
  have hmax : max (log b) L - log b = max 0 (L - log b) := by
    by_cases h : L ≤ log b
    · rw [max_eq_left h, max_eq_left (sub_nonpos.mpr h), sub_self]
    · rw [max_eq_right (le_of_not_ge h), max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
  linarith only [hlog, hmax]

end Real

namespace Matrix.MeanTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive floor gives uniform logarithmic bounds for every mean
tree, including trees with zero terminal weights. The upper exponent bound
is independent of the terminal probabilities.
Source: `07-comparators.tex`, lines 615–629. -/
theorem weighted_log_add_half_exp_bounds (T : MeanTree ι)
    {b : ℝ} (hb : 0 < b) (L : ι → ℝ) {U : ℝ} (hU : ∀ j, L j ≤ U) :
    let ell := ∑ j, T.weight j * Real.log (b + Real.exp (L j) / 2)
    (∑ j, T.weight j * L j) - Real.log 2 ≤ ell ∧
      0 ≤ ell - Real.log b ∧
      ell - Real.log b ≤ max 0 (U - Real.log b) + Real.log (3 / 2) := by
  intro ell
  have hconst (c : ℝ) : (∑ j, T.weight j * c) = c := by
    rw [← Finset.sum_mul, T.sum_weight, one_mul]
  have hlower := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    mul_le_mul_of_nonneg_left
      (Real.sub_log_two_le_log_add_half_exp hb.le (L j)) (T.weight_nonneg j)
  have hfloor := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    mul_le_mul_of_nonneg_left
      (Real.log_le_log hb
        (le_add_of_nonneg_right ((half_pos (Real.exp_pos (L j))).le)))
      (T.weight_nonneg j)
  have hupper := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    mul_le_mul_of_nonneg_left
      ((Real.log_add_half_exp_sub_log_le hb (L j)).trans
        (add_le_add_left (max_le_max le_rfl (sub_le_sub_right (hU j) _)) _))
      (T.weight_nonneg j)
  simp only [mul_sub, Finset.sum_sub_distrib, hconst] at hlower hfloor hupper
  exact ⟨hlower, sub_nonneg.mpr hfloor, hupper⟩

end Matrix.MeanTree
