/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.FiniteUniformConditioning

/-! Equal atoms on an event need not extend to equal atoms outside it. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace FiniteUniformConditioningTest

noncomputable section

private def mixedMeasure : Measure ℕ :=
  Measure.dirac 0 + Measure.dirac 1 + (2 : ℝ≥0) • Measure.dirac 2

private instance : IsFiniteMeasure mixedMeasure := by
  unfold mixedMeasure
  infer_instance

private lemma equal_atoms (x : ℕ) (hx : x ∈ ({0, 1} : Set ℕ)) :
    mixedMeasure {x} = 1 := by
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num [mixedMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  · have : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    norm_num [mixedMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

-- The measure is deliberately not uniform outside the conditioning event.
example : mixedMeasure {0} = 1 ∧ mixedMeasure {2} = 2 := by
  norm_num [mixedMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

-- The finite-event mass is obtained from the common atomic mass.
example : mixedMeasure {0, 1} = 2 := by
  rw [measure_eq_count_mul_of_finite_constant_singletons mixedMeasure
    (by simp : ({0, 1} : Set ℕ).Finite) equal_atoms]
  norm_num [Measure.count_apply, Set.encard_insert_of_notMem]

-- The restriction theorem does not assume normalization of the ambient measure.
example : mixedMeasure.restrict {0, 1} = Measure.count.restrict {0, 1} := by
  simpa using restrict_eq_smul_count_of_finite_constant_singletons mixedMeasure
    (by simp : ({0, 1} : Set ℕ).Finite) equal_atoms

-- Conditioning removes the unequal outside mass and gives the uniform law.
example : cond mixedMeasure {0, 1} = uniformOn {0, 1} := by
  apply cond_eq_uniformOn_of_finite_constant_singletons mixedMeasure
    (by simp : ({0, 1} : Set ℕ).Finite) equal_atoms
  norm_num [mixedMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

-- Equal zero atoms on a nonempty event do not justify conditional uniformity.
example : cond (0 : Measure ℕ) {0, 1} ≠ uniformOn {0, 1} := by
  intro h
  have hu := uniformOn_self (by simp : ({0, 1} : Set ℕ).Finite)
    (by simp : ({0, 1} : Set ℕ).Nonempty)
  rw [← h] at hu
  simp [ProbabilityTheory.cond] at hu

end

end FiniteUniformConditioningTest
