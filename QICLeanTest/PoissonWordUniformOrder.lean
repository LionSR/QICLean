/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordUniformOrder

/-! Actual conditional word masses, null events, and count-and-order reconstruction. -/

open MeasureTheory PoissonWord ProbabilityTheory
open scoped BigOperators ENNReal NNReal Nat

namespace PoissonWordUniformOrderTest

private def repeatedWord : Word (Fin 2) := ⟨3, ![0, 1, 0]⟩

private lemma repeatedWord_count : countVector repeatedWord = ![2, 1] := by
  change countVector (⟨3, ![0, 1, 0]⟩ : Word (Fin 2)) = ![2, 1]
  ext i
  fin_cases i <;>
    simp [countVector, WordMultiplicity.countsFinsupp, Fin.sum_univ_three]

private lemma repeatedCounts_ne_zero : (![2, 1] : Fin 2 → ℕ) ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num at this

private lemma repeatedEvent_count : Measure.count (countEvent ![2, 1]) = 3 := by
  rw [Measure.count_apply (finite_countEvent _).measurableSet, ← Set.coe_fintypeCard]
  change ((Fintype.card (countFiber ![2, 1]) : ℕ∞) : ℝ≥0∞) = 3
  rw [card_countFiber_eq_factorial]
  norm_num [Fin.sum_univ_two, Fin.prod_univ_two]

-- Repeated labels produce three compatible orderings, each with conditional mass 1/3.
example (t : ℝ≥0) (ht : 0 < t) :
    cond (measure (Fin 2) t) (countEvent ![2, 1]) {repeatedWord} = 1 / 3 := by
  rw [cond_countEvent_of_pos t ht, uniformOn,
    cond_apply (finite_countEvent _).measurableSet]
  have hw : {repeatedWord} ⊆ countEvent ![2, 1] :=
    Set.singleton_subset_iff.mpr repeatedWord_count
  rw [Set.inter_eq_right.mpr hw, repeatedEvent_count, Measure.count_singleton]
  simp [one_div]

-- The event being conditioned on has positive mass at every positive time.
example (t : ℝ≥0) (ht : 0 < t) : 0 < measure (Fin 2) t (countEvent ![2, 1]) :=
  measure_countEvent_pos t ht _

-- The same nonzero count event is null at time zero, so its conditional law is zero.
example : measure (Fin 2) 0 (countEvent ![2, 1]) = 0 :=
  measure_countEvent_zero_time_of_ne _ repeatedCounts_ne_zero

example : cond (measure (Fin 2) 0) (countEvent ![2, 1]) = 0 :=
  cond_countEvent_zero_time_of_ne _ repeatedCounts_ne_zero

-- Uniformity on a nonempty fiber is false when that fiber is a null event.
example : cond (measure (Fin 2) 0) (countEvent ![2, 1]) ≠
    uniformOn (countEvent ![2, 1]) := by
  rw [cond_countEvent_zero_time_of_ne _ repeatedCounts_ne_zero]
  intro h
  have hu := uniformOn_self (finite_countEvent ![2, 1]) (countEvent_nonempty ![2, 1])
  rw [← h] at hu
  simp at hu

-- The zero vector remains a valid conditioning event at time zero.
example : cond (measure (Fin 2) 0) (countEvent 0) = uniformOn (countEvent 0) := by
  apply cond_countEvent
  simp [measure_zero, countEvent, Measure.dirac_apply']

-- Empty is allowed at all times, including zero, without a positive-time hypothesis.
example (t : ℝ≥0) (n : Empty → ℕ) :
    cond (measure Empty t) (countEvent n) = uniformOn (countEvent n) := by
  apply cond_countEvent
  rw [measure_countEvent_eq_prod]
  simp

-- This equality reconstructs the actual word measure from the defined sampler.
example (t : ℝ≥0) : countsThenUniform (ι := Fin 2) t = measure (Fin 2) t :=
  countsThenUniform_eq_measure t

-- In particular, a word containing a repeated label has its original atomic weight.
example (t : ℝ≥0) : countsThenUniform (ι := Fin 2) t {repeatedWord} =
    ENNReal.ofReal (weight (Fin 2) t 3) := by
  rw [countsThenUniform_eq_measure, PoissonWord.measure_singleton]
  rfl

-- At zero time the reconstruction puts all mass on the empty word.
example : countsThenUniform (ι := Fin 2) 0 = Measure.dirac (nil : Word (Fin 2)) := by
  rw [countsThenUniform_eq_measure, measure_zero]

-- With no labels, the same reconstruction is concentrated on the empty word at every time.
example (t : ℝ≥0) : countsThenUniform (ι := Empty) t =
    Measure.dirac (nil : Word Empty) := by
  rw [countsThenUniform_eq_measure, measure_of_isEmpty]

-- The named instance supplies probability normalization for the actual sampler.
example (t : ℝ≥0) : IsProbabilityMeasure (countsThenUniform (ι := Fin 2) t) :=
  inferInstance

example (t : ℝ≥0) : countsThenUniform (ι := Empty) t Set.univ = 1 :=
  measure_univ

end PoissonWordUniformOrderTest
