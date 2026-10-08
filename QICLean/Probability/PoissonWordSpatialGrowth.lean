/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ExponentialDistanceProfile
import QICLean.Probability.PoissonWordWeightedGrowth

/-!
# Spatial growth of observables on Poisson words

A weighted row estimate for a nonnegative kernel and an initial bound by the
indicator of a set imply exponential decay of the expected observable in the
distance from that set. The metric supersolution is proved from the extended
triangle inequality. On components at infinite distance, every word has zero
observable, not just zero expectation.

This is the finite-alphabet, finite-site probabilistic consequence of the
metric argument in `09-amplification.tex`, lines 159–188. The hypotheses still
require the actual summed append-increment estimate; this module does not
construct the physical oscillation kernel or chronological clock process.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace PoissonWord

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [PseudoEMetricSpace κ]

/-- A literal initial-support bound and a weighted metric row bound imply
integrability and spatial exponential decay under the actual Poisson-word law.
The profile is zero at infinite distance, including for an empty support set. -/
theorem integrable_and_integral_le_of_spatial_growth (t : ℝ≥0)
    (f : Word ι → κ → ℝ) (A : κ → κ → ℝ) (S : Set κ) {a α v C : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hinitial : ∀ y, f nil y ≤ C * S.indicator (fun _ ↦ (1 : ℝ)) y)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hsupport : ∀ y z, edist y z = ∞ → A y z = 0)
    (hrow : ∀ y, (∑ z : κ, A y z * Real.exp (a * (edist y z).toReal ^ α)) ≤ v)
    (y : κ) :
    Integrable (fun u ↦ f u y) (measure ι t) ∧
      (∫ u, f u y ∂measure ι t) ≤
        Real.exp (v * t) * C * Metric.exponentialDistanceProfile S a α y := by
  apply integrable_and_integral_le_of_weighted_growth t f A
    (Metric.exponentialDistanceProfile S a α) hf hA
    (Metric.exponentialDistanceProfile_nonneg S a α) hv hC
  · intro z
    exact (hinitial z).trans (mul_le_mul_of_nonneg_left
      (Metric.indicator_one_le_exponentialDistanceProfile S a hα z) hC)
  · exact hstep
  · exact Metric.sum_mul_exponentialDistanceProfile_le S A ha hα hα₁ hA hsupport hrow

/-- At infinite distance from the initial support, the observable vanishes at
every actual word. In particular, an empty initial support stays identically zero. -/
theorem eq_zero_of_spatial_growth_of_infEDist_eq_top
    (f : Word ι → κ → ℝ) (A : κ → κ → ℝ) (S : Set κ) {a α v C : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hinitial : ∀ y, f nil y ≤ C * S.indicator (fun _ ↦ (1 : ℝ)) y)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hsupport : ∀ y z, edist y z = ∞ → A y z = 0)
    (hrow : ∀ y, (∑ z : κ, A y z * Real.exp (a * (edist y z).toReal ^ α)) ≤ v)
    (y : κ) (hy : Metric.infEDist y S = ∞) (u : Word ι) : f u y = 0 := by
  apply eq_zero_of_weighted_growth_of_profile_eq_zero f A
    (Metric.exponentialDistanceProfile S a α) hf hA hv hC
  · intro z
    exact (hinitial z).trans (mul_le_mul_of_nonneg_left
      (Metric.indicator_one_le_exponentialDistanceProfile S a hα z) hC)
  · exact hstep
  · exact Metric.sum_mul_exponentialDistanceProfile_le S A ha hα hα₁ hA hsupport hrow
  · exact (Metric.exponentialDistanceProfile_eq_zero_iff S a α y).2 hy

end PoissonWord
