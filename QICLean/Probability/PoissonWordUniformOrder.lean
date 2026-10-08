/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.FiniteUniformConditioning
import QICLean.Probability.PoissonWordIndependentCounts

/-!
# Independent counts followed by a uniform label ordering

Conditioning the actual Poissonized word law on a non-null count event is
uniform over the compatible words. Conversely, sampling independent Poisson
counts and a uniform compatible word reconstructs that law, including at time
zero. Null conditioning events are treated separately.

This is a fixed-time characterization relevant to `09-amplification.tex`,
lines 49–54 and 237–253 of the area-law manuscript. It does not construct
event times, a process with independent increments, or a pathwise clock coupling.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace PoissonWord

variable {ι : Type*} [Fintype ι]

/-- The actual word law is uniform conditional on any non-null count event. -/
theorem cond_countEvent (t : ℝ≥0) (n : ι → ℕ)
    (h : measure ι t (countEvent n) ≠ 0) :
    ProbabilityTheory.cond (measure ι t) (countEvent n) =
      ProbabilityTheory.uniformOn (countEvent n) := by
  apply ProbabilityTheory.cond_eq_uniformOn_of_finite_constant_singletons
    (measure ι t) (finite_countEvent n) (c := ENNReal.ofReal (weight ι t (∑ i, n i)))
  · intro w hw
    rw [measure_singleton, length_eq_sum_of_countVector_eq hw]
  · exact h

/-- At positive time every finite count vector has positive probability. -/
theorem measure_countEvent_pos (t : ℝ≥0) (ht : 0 < t) (n : ι → ℕ) :
    0 < measure ι t (countEvent n) := by
  rw [measure_countEvent]
  apply ENNReal.mul_pos_iff.mpr
  constructor
  · exact_mod_cast Fintype.card_pos_iff.mpr (countFiber_nonempty n)
  · apply ENNReal.ofReal_pos.mpr
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    unfold weight
    positivity

/-- At positive time the conditional word law is uniform for every count vector. -/
theorem cond_countEvent_of_pos (t : ℝ≥0) (ht : 0 < t) (n : ι → ℕ) :
    ProbabilityTheory.cond (measure ι t) (countEvent n) =
      ProbabilityTheory.uniformOn (countEvent n) :=
  cond_countEvent t n (ne_of_gt (measure_countEvent_pos t ht n))

/-- A nonzero count vector has zero probability at time zero. -/
theorem measure_countEvent_zero_time_of_ne (n : ι → ℕ) (hn : n ≠ 0) :
    measure ι 0 (countEvent n) = 0 := by
  classical
  simp [measure_zero, countEvent, Measure.dirac_apply', Ne.symm hn]

/-- Conditioning on an impossible nonzero count at time zero gives the zero measure. -/
theorem cond_countEvent_zero_time_of_ne (n : ι → ℕ) (hn : n ≠ 0) :
    ProbabilityTheory.cond (measure ι 0) (countEvent n) = 0 :=
  ProbabilityTheory.cond_eq_zero_of_meas_eq_zero (measure_countEvent_zero_time_of_ne n hn)

/-- First sample independent Poisson counts, then a uniformly ordered compatible word. -/
def countsThenUniform (t : ℝ≥0) : Measure (Word ι) :=
  Measure.sum (fun n : ι → ℕ =>
    (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure t)) {n} •
      ProbabilityTheory.uniformOn (countEvent n))

/-- Independent counts followed by uniform ordering give exactly the original word law. -/
theorem countsThenUniform_eq_measure (t : ℝ≥0) : countsThenUniform (ι := ι) t = measure ι t := by
  classical
  apply Measure.ext_of_singleton
  intro w
  rw [countsThenUniform, Measure.sum_apply _ (measurableSet_singleton w),
    tsum_eq_single (countVector w)]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton,
      ← measure_countEvent_eq_prod]
    have hw : {w} ⊆ countEvent (countVector w) := Set.singleton_subset_iff.mpr rfl
    by_cases h : measure ι t (countEvent (countVector w)) = 0
    · have hz : measure ι t {w} = 0 := measure_mono_null hw h
      simp [h, hz]
    · rw [← cond_countEvent t (countVector w) h, mul_comm,
        ProbabilityTheory.cond_mul_eq_inter (finite_countEvent _).measurableSet]
      rw [Set.inter_eq_right.mpr hw]
  · intro n hn
    have hw : w ∉ countEvent n := by
      simpa only [countEvent, Set.mem_ofPred_eq] using Ne.symm hn
    have hz : ProbabilityTheory.uniformOn (countEvent n) {w} = 0 :=
      (ProbabilityTheory.uniformOn_eq_zero_iff (finite_countEvent n)).mpr
        (Set.inter_singleton_eq_empty.mpr hw)
    simp [Measure.smul_apply, hz]

/-- The count-and-order sampler is a probability measure at every nonnegative time. -/
instance instIsProbabilityMeasureCountsThenUniform (t : ℝ≥0) :
    IsProbabilityMeasure (countsThenUniform (ι := ι) t) := by
  rw [countsThenUniform_eq_measure]
  infer_instance

end PoissonWord
