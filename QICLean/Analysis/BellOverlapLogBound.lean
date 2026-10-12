/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The logarithmic bound obtained from a Bell overlap

An inverse-polynomial Bell overlap and the cutoff inverse-norm estimate give
an explicit upper bound on the negative logarithm of the squared norm.
The logarithmic remainder is independent of the matrix mean tree and the
exponent in the interval under consideration. All dimensions and polynomial
degrees are fixed before the replica count tends to infinity.

This is a scalar implication. The physical application must supply the
overlap inequality for the original prevector and the same auxiliary labels.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 153–163 and 332–381,
`comparator:rough-upper`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter
open scoped Topology

noncomputable section

namespace Real

/-- The logarithmic error in the upper comparison, uniform in the inverse-power
exponent and the weighted mean tree. Source: area-law manuscript,
`07-comparators.tex`, lines 332–381 and 659–667. -/
def bellOverlapRemainder (d : ℕ) (c : ℝ) (K k : ℕ) : ℝ :=
  (Real.log 4 + ((d : ℝ) ^ 2 + c * (K : ℝ)) * Real.log ((k : ℝ) + 2)) / (k : ℝ)

/-- The squared Bell overlap and the inverse-power coefficient give the rough
upper logarithmic estimate. Positivity of the squared norm is derived from
the overlap inequality. This scalar result does not choose a prevector or
an auxiliary label. Source: area-law manuscript, `07-comparators.tex`,
lines 153–163 and 332–381, `comparator:rough-upper`. -/
theorem neg_log_div_le_of_bell_overlap_bound (d K k : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (z c t B s r : ℝ) (hz : 0 < z) (hc : 0 ≤ c) (hs : 2 * s ∈ Set.Icc (0 : ℝ) 1)
    (hbound : (z / (d : ℝ) ^ 2) ^ k /
        (4 * (((k + 1 : ℕ) : ℝ) ^ (d ^ 2))) ≤
      ((((k : ℝ) + 2) ^ (c * (K : ℝ)) *
        Real.exp (4 * t * (K : ℝ) * (k : ℝ) * B)) ^ (2 * s)) * r) :
    0 < r ∧ -Real.log r / (k : ℝ) ≤
      2 * Real.log (d : ℝ) - Real.log z + 8 * s * t * (K : ℝ) * B +
        bellOverlapRemainder d c K k := by
  have hleft : 0 < (z / (d : ℝ) ^ 2) ^ k /
      (4 * (((k + 1 : ℕ) : ℝ) ^ (d ^ 2))) := by positivity
  have hcoef : 0 < (((k : ℝ) + 2) ^ (c * (K : ℝ)) *
      Real.exp (4 * t * (K : ℝ) * (k : ℝ) * B)) ^ (2 * s) := by positivity
  have hr : 0 < r := pos_of_mul_pos_right (hleft.trans_le hbound) hcoef.le
  have hlog := Real.log_le_log hleft hbound
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Real.log_exp, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at hlog
  have hdim := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2))
    (sq_nonneg (d : ℝ))
  have hpoly := mul_le_mul_of_nonneg_right hs.2
    (mul_nonneg (mul_nonneg hc (Nat.cast_nonneg K))
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k] : 1 ≤ (k : ℝ) + 2)))
  refine ⟨hr, (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_le_iff.mp hk))).2 ?_⟩
  rw [bellOverlapRemainder, add_mul,
    div_mul_cancel₀ _ (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_le_iff.mp hk)))]
  nlinarith only [hlog, hdim, hpoly]

end Real
