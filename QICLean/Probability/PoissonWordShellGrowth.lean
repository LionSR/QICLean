/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StretchedBallKernel
import QICLean.Probability.PoissonWordSpatialGrowth

/-!
# Spatial growth from literal stretched-exponential shells

The actual quadratic anchor-label and site-ball counts calibrate the spatial
growth estimate for nonnegative observables on actual Poisson words. The
spatial rate is `c / (2 * 2 ^ α)` and the temporal rate uses the convergent
fourth shell moment at rate `c / 2`; neither formula uses the total number of
labels or sites. The literal shell kernel supplies its own nonnegativity,
infinite-distance support, and weighted row bound.

This assembles the generic stochastic propagation argument in
`09-amplification.tex`, lines 141–188, at source revision `adc7f124`. The actual
summed append-increment estimate is a hypothesis. Identifying a physical
oscillation observable, its graph geometry, and its chronological clocks
remains separate.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace PoissonWord

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [PseudoEMetricSpace κ]

open Classical in
/-- Literal quadratic counts and an append estimate for the actual shell
kernel give integrable expectations with explicit spatial and temporal rates.
At infinite distance from the initial support, every word has zero observable. -/
theorem integrable_and_integral_le_of_shell_growth (t : ℝ≥0)
    (f : Word ι → κ → ℝ) (anchor : ι → κ) (S : Set κ) {C c α B V M : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hf : ∀ u y, 0 ≤ f u y)
    (hinitial : ∀ y, f nil y ≤ M * S.indicator (fun _ ↦ (1 : ℝ)) y)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, Metric.stretchedBallKernel anchor C c α y z * f u z)
    (hlabels : ∀ (n : ℕ) (y : κ),
      ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        B * (1 + (n : ℝ)) ^ 2)
    (hballs : ∀ (n : ℕ) (i : ι),
      ((Finset.univ.filter fun z : κ ↦ edist z (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        V * (1 + (n : ℝ)) ^ 2) :
    let a := c / (2 * 2 ^ α)
    let v := C * B * V * ∑' n : ℕ,
      (1 + (n : ℝ)) ^ 4 * Real.exp (-(c / 2) * (n : ℝ) ^ α)
    0 < a ∧ 0 ≤ v ∧
      (∀ y : κ, Integrable (fun u ↦ f u y) (measure ι t) ∧
        (∫ u, f u y ∂measure ι t) ≤
          Real.exp (v * t) * M * Metric.exponentialDistanceProfile S a α y) ∧
      ∀ y : κ, Metric.infEDist y S = ∞ → ∀ u : Word ι, f u y = 0 := by
  dsimp only
  obtain ⟨ha, hrow⟩ := Metric.sum_stretchedBallKernel_mul_exp_half_rate_le
    anchor hC hc hα hB hV hlabels hballs
  have hv : 0 ≤ C * B * V * ∑' n : ℕ,
      (1 + (n : ℝ)) ^ 4 * Real.exp (-(c / 2) * (n : ℝ) ^ α) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg hC hB) hV)
    exact tsum_nonneg fun n ↦ mul_nonneg (by positivity) (Real.exp_pos _).le
  have hA := Metric.stretchedBallKernel_nonneg anchor (c := c) (α := α) hC
  have hsupport : ∀ y z : κ, edist y z = ∞ →
      Metric.stretchedBallKernel anchor C c α y z = 0 :=
    fun _ _ hyz ↦ Metric.stretchedBallKernel_eq_zero_of_edist_eq_top anchor C c α hyz
  refine ⟨ha, hv, ?_, ?_⟩
  · intro y
    exact integrable_and_integral_le_of_spatial_growth t f
      (Metric.stretchedBallKernel anchor C c α) S ha.le hα hα₁ hf hA hv hM
      hinitial hstep hsupport hrow y
  · intro y hy u
    exact eq_zero_of_spatial_growth_of_infEDist_eq_top f
      (Metric.stretchedBallKernel anchor C c α) S ha.le hα hα₁ hf hA hv hM
      hinitial hstep hsupport hrow y hy u

end PoissonWord
