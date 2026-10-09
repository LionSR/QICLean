/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordSpatialGrowth

/-! Actual initial support, finite-distance exponential shape, and empty support. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal

namespace PoissonWordSpatialGrowthTest

-- An empty support forces every actual word observable to vanish.
example {ι κ : Type*} [Fintype ι] [Fintype κ] [PseudoEMetricSpace κ]
    (f : Word ι → κ → ℝ) (A : κ → κ → ℝ) {a α v C : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hv : 0 ≤ v) (hC : 0 ≤ C) (h0 : ∀ y, f nil y ≤ 0)
    (hs : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hsupport : ∀ y z, edist y z = ∞ → A y z = 0)
    (hrow : ∀ y, (∑ z : κ, A y z * Real.exp (a * (edist y z).toReal ^ α)) ≤ v)
    (y : κ) (u : Word ι) : f u y = 0 := by
  apply eq_zero_of_spatial_growth_of_infEDist_eq_top f A ∅ ha hα hα₁ hf hA hv hC
    (fun z ↦ by simpa using h0 z) hs hsupport hrow y (by simp) u

-- Finite distance gives the literal exponential appearing in the manuscript.
example {ι κ : Type*} [Fintype ι] [Fintype κ] [PseudoEMetricSpace κ]
    (T : ℝ≥0) (f : Word ι → κ → ℝ) (A : κ → κ → ℝ) (S : Set κ) {a α v C : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hv : 0 ≤ v) (hC : 0 ≤ C)
    (h0 : ∀ y, f nil y ≤ C * S.indicator (fun _ ↦ (1 : ℝ)) y)
    (hs : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hsupport : ∀ y z, edist y z = ∞ → A y z = 0)
    (hrow : ∀ y, (∑ z : κ, A y z * Real.exp (a * (edist y z).toReal ^ α)) ≤ v)
    (y : κ) (hy : Metric.infEDist y S ≠ ∞) :
    Integrable (fun u ↦ f u y) (measure ι T) ∧
      (∫ u, f u y ∂measure ι T) ≤
        C * Real.exp (v * T - a * (Metric.infEDist y S).toReal ^ α) := by
  have h := integrable_and_integral_le_of_spatial_growth T f A S ha hα hα₁
    hf hA hv hC h0 hs hsupport hrow y
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [Metric.exponentialDistanceProfile_of_ne_top S a α y hy, sub_eq_add_neg,
    Real.exp_add]
  ring

-- With no event labels the spatial bound has zero temporal rate.
example {κ : Type*} [Fintype κ] [PseudoEMetricSpace κ]
    (T : ℝ≥0) (f : Word (Fin 0) → κ → ℝ) (S : Set κ) {a α C : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hf : ∀ u y, 0 ≤ f u y) (hC : 0 ≤ C)
    (h0 : ∀ y, f nil y ≤ C * S.indicator (fun _ ↦ (1 : ℝ)) y) (y : κ) :
    Integrable (fun u ↦ f u y) (measure (Fin 0) T) ∧
      (∫ u, f u y ∂measure (Fin 0) T) ≤
        C * Metric.exponentialDistanceProfile S a α y := by
  have h := integrable_and_integral_le_of_spatial_growth T f (fun _ _ ↦ 0) S
    ha hα hα₁ hf (fun _ _ ↦ le_rfl) (v := 0) le_rfl hC h0
    (fun _ _ ↦ by simp) (fun _ _ _ ↦ rfl) (fun _ ↦ by simp) y
  simpa using h

end PoissonWordSpatialGrowthTest
