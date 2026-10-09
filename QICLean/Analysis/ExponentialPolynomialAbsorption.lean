/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential errors below inverse polynomial mass

An exponentially decreasing error is eventually smaller than the retained
Schur-label mass, including the shift in the copy number. This scalar fact
does not assert any concentration estimate for a state.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–354,
  `comparator:rough-overlap`.

-/

open Filter Topology

namespace Real

/-- Every fixed real multiple of a decreasing exponential is eventually below
one quarter of the shifted inverse polynomial. In the retained-mass argument
the multiple is the number of imposed cutoffs. The conclusion includes zero
multiple and zero polynomial degree. -/
theorem eventually_mul_exp_neg_le_inv_four_pow_add_one
    {c : ℝ} (hc : 0 < c) (m : ℝ) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      m * exp (-c * (k : ℝ)) ≤ 1 / (4 * (((k + 1 : ℕ) : ℝ) ^ d)) := by
  have hshift : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto
      (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ d *
        exp (-c * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) c hc).comp hshift
  have hscaled : Tendsto
      (fun k : ℕ ↦ (4 * m * exp c) *
        (((k + 1 : ℕ) : ℝ) ^ d * exp (-c * ((k + 1 : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hdecay.const_mul (4 * m * exp c)
  filter_upwards [hscaled.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hk
  have hfactor : exp c * exp (-c * ((k + 1 : ℕ) : ℝ)) =
      exp (-c * (k : ℝ)) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((k + 1 : ℕ) : ℝ) ^ d)).2
  calc
    (m * exp (-c * (k : ℝ))) * (4 * ((k + 1 : ℕ) : ℝ) ^ d) =
        (4 * m * exp c) *
          (((k + 1 : ℕ) : ℝ) ^ d * exp (-c * ((k + 1 : ℕ) : ℝ))) := by
      rw [← hfactor]
      ring
    _ ≤ 1 := hk.le

end Real
