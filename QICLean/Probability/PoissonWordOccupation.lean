/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordInsertion
import QICLean.Probability.PoissonWordPartition

/-!
# Occupation of retained prefixes at marked letters

The prefix before a marked letter has the actual word law at its insertion
time. Filtering that prefix by a predicate gives the retained-alphabet law.
This derives the nonnegative rate/time identity for omitted letters from the
same full-word sample, without assuming independence of random prefixes.

This supplies the probability step at `09-amplification.tex`, lines 203–209.
The prefix-sensitive operator telescope and spatial defect estimates remain
separate inputs; no clock path, propagation, or spatial omission bound is
constructed here.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace PoissonWord

variable {ι : Type*} [Fintype ι]

/-- A retained-prefix observable is averaged using the actual retained-alphabet law. -/
theorem lintegral_sum_partition_prefix (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      F (partitionWords p (take w j)).1 (w.2 j) ∂measure ι T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫⁻ u, F u i ∂measure {i // p i} (Real.toNNReal s) := by
  rw [lintegral_sum_prefix T (fun u i => F (partitionWords p u).1 i)]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_partitionWords_fst p (Real.toNNReal s)]
  exact (lintegral_map (f := fun u : Word {i // p i} => F u i)
    (g := fun u : Word ι => (partitionWords p u).1)
    (μ := measure ι (Real.toNNReal s))
    Measurable.of_discrete Measurable.of_discrete).symm

/-- Omitted letters are integrated against retained prefixes at each insertion time. -/
theorem lintegral_sum_omitted_partition_prefix (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j)
        ∂measure ι T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ),
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
          ∫⁻ u, F u i ∂measure {i // p i} (Real.toNNReal s) := by
  classical
  calc
    _ = ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫⁻ u, (if p i then 0 else F u i)
          ∂measure {i // p i} (Real.toNNReal s) :=
      lintegral_sum_partition_prefix p T (fun u i => if p i then 0 else F u i)
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s _
      dsimp only
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i <;> simp [hi]

/-- The expected number of omitted letters is their alphabet size times the duration. -/
theorem lintegral_omitted_count (p : ι → Prop) [DecidablePred p] (T : ℝ≥0) :
    (∫⁻ w, ∑ j : Fin w.1, if p (w.2 j) then (0 : ℝ≥0∞) else 1 ∂measure ι T) =
      ((Finset.univ.filter (fun i => ¬p i)).card : ℝ≥0∞) * T := by
  simpa only [lintegral_const, measure_univ, mul_one, Finset.sum_const,
    nsmul_eq_mul, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_coe_nnreal] using
    lintegral_sum_omitted_partition_prefix p T (fun _ _ => 1)

end PoissonWord
