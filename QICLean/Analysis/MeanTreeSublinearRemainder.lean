/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring

/-!
# Sublinear remainders in the rough lower norm comparison

At fixed physical and auxiliary dimensions, the number of bands, inverse-power
exponent and all polynomial degrees are fixed. If the auxiliary-label error is
sublinear in the replica count, the logarithmic and absolute-value errors in
the rough lower norm comparison vanish after division by that count.

This is a scalar implication. It neither constructs the auxiliary labels nor
establishes the physical norm comparison. The label error may be signed, and
no sign conditions on the fixed coefficients are needed for the limit.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 8, `07-comparators.tex`,
`comparator:rough-lower`, lines 153–169 and 585–651,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter
open scoped Topology

namespace Matrix.MeanTree

/-- Every fixed real shift of the logarithm is sublinear along natural replica
counts. This is an auxiliary to the logarithmic errors in
`07-comparators.tex`, lines 585–651. -/
private theorem tendsto_shifted_log_div_nat (a : ℝ) :
    Tendsto (fun k : ℕ ↦ Real.log ((k : ℝ) + a) / (k : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun k : ℕ ↦ (k : ℝ) + a) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hcomp :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-a) 1 one_ne_zero).comp hshift
  refine hcomp.congr' (Eventually.of_forall (fun k ↦ ?_))
  simp only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right]

/-- The explicit logarithmic and auxiliary-label remainder in the rough lower
norm comparison is sublinear when the label error is sublinear. All five real
coefficients are fixed before the replica count. Source:
`07-comparators.tex`, `comparator:rough-lower`, lines 153–169 and 585–651. -/
theorem tendsto_rough_lower_remainder_div_nat
    (s G t c C_f : ℝ) {ε : ℕ → ℝ}
    (hε : Tendsto (fun k : ℕ ↦ ε k / (k : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ ↦
      (2 * s * G * (2 * |Real.log ((k : ℝ) + 1) +
        c * Real.log ((k : ℝ) + 2) + 2 * t * ε k| +
        C_f * Real.log ((k : ℝ) + 2) + 2 * Real.log 2 + Real.log (3 / 2))) /
        (k : ℝ)) atTop (𝓝 0) := by
  have hlog₁ := tendsto_shifted_log_div_nat 1
  have hlog₂ := tendsto_shifted_log_div_nat 2
  have hinner : Tendsto (fun k : ℕ ↦
      (Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * t * ε k) / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, add_zero, mul_zero] using
      (hlog₁.add (hlog₂.const_mul c)).add (hε.const_mul (2 * t))
  have habs : Tendsto (fun k : ℕ ↦
      |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * t * ε k| / (k : ℝ)) atTop (𝓝 0) := by
    have hnorm := hinner.norm
    simp only [norm_zero] at hnorm
    refine hnorm.congr' (Eventually.of_forall (fun k ↦ ?_))
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg k)]
  have hinv : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun k : ℕ ↦
      (2 * Real.log 2 + Real.log (3 / 2)) / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinv.const_mul (2 * Real.log 2 + Real.log (3 / 2))
  have hnormalized : Tendsto (fun k : ℕ ↦
      2 * s * G * (2 * (|Real.log ((k : ℝ) + 1) +
        c * Real.log ((k : ℝ) + 2) + 2 * t * ε k| / (k : ℝ)) +
        C_f * (Real.log ((k : ℝ) + 2) / (k : ℝ)) +
        (2 * Real.log 2 + Real.log (3 / 2)) / (k : ℝ)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      (((habs.const_mul 2).add (hlog₂.const_mul C_f)).add hconst).const_mul (2 * s * G)
  exact hnormalized.congr' (Eventually.of_forall (fun k ↦ by ring))

end Matrix.MeanTree
