/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Probability.UniformOn

/-!
# Conditioning equal atomic masses on a finite event

Equal singleton masses on a finite event give a scalar multiple of counting
measure after restriction. Conditioning on a positive-mass event therefore
gives its uniform measure. No equality with the conditional law is assumed.

This generic fact supplies the conditional-ordering step for finite Poissonized
words. Null conditioning events are deliberately excluded from the uniformity
conclusion.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Constant atomic masses sum to the counting mass times the common value. -/
theorem measure_eq_count_mul_of_finite_constant_singletons (μ : Measure Ω)
    {s : Set Ω} (hs : s.Finite) {c : ℝ≥0∞} (hc : ∀ x ∈ s, μ {x} = c) :
    μ s = Measure.count s * c := by
  classical
  calc
    μ s = ∑ x ∈ hs.toFinset, μ {x} := by simp
    _ = ∑ _x ∈ hs.toFinset, c :=
      Finset.sum_congr rfl fun x hx => hc x (hs.mem_toFinset.mp hx)
    _ = (hs.toFinset.card : ℝ≥0∞) * c := by simp [nsmul_eq_mul]
    _ = Measure.count s * c := by rw [Measure.count_apply_finite s hs]

/-- Restricting constant atomic masses to a finite event gives scaled counting measure. -/
theorem restrict_eq_smul_count_of_finite_constant_singletons (μ : Measure Ω)
    {s : Set Ω} (hs : s.Finite) {c : ℝ≥0∞} (hc : ∀ x ∈ s, μ {x} = c) :
    μ.restrict s = c • Measure.count.restrict s := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.smul_apply, Measure.restrict_apply ht]
  simpa only [smul_eq_mul, mul_comm] using
    measure_eq_count_mul_of_finite_constant_singletons μ (hs.inter_of_right t)
      (fun x hx => hc x hx.2)

/-- Conditioning equal atomic masses on a non-null finite event is uniform. -/
theorem cond_eq_uniformOn_of_finite_constant_singletons (μ : Measure Ω) [IsFiniteMeasure μ]
    {s : Set Ω} (hs : s.Finite) {c : ℝ≥0∞} (hc : ∀ x ∈ s, μ {x} = c)
    (hμs : μ s ≠ 0) : cond μ s = uniformOn s := by
  classical
  have hmass := measure_eq_count_mul_of_finite_constant_singletons μ hs hc
  have hc0 : c ≠ 0 := by
    intro h
    exact hμs (by simpa [h] using hmass)
  have hsne : s.Nonempty := by
    by_contra h
    have hz : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    exact hμs (by simp [hz])
  obtain ⟨x, hx⟩ := hsne
  have hctop : c ≠ ∞ := by
    rw [← hc x hx]
    exact measure_ne_top μ {x}
  have hntop : Measure.count s ≠ ∞ := (Measure.count_apply_lt_top.2 hs).ne
  rw [uniformOn, cond, cond,
    restrict_eq_smul_count_of_finite_constant_singletons μ hs hc,
    smul_smul, hmass]
  congr 1
  rw [ENNReal.mul_inv (Or.inr hctop) (Or.inl hntop), mul_assoc,
    ENNReal.inv_mul_cancel hc0 hctop, mul_one]

end ProbabilityTheory
