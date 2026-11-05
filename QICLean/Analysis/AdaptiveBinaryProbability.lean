/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.AdaptiveSamplingProbability

/-!
# Combining errors at a binary merge

Two independent child histories and a fresh parent sample have failure
probability at most the sum of their three error budgets. The parent bound
is required only when both children have succeeded. This is the
measure-theoretic binary step for the interval recursion in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
The actual measurable parent map and its section bound are supplied
by the physical construction.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The failure of either independent child has at most the sum of its
individual failure probabilities. No measurability of the child sets
is needed for this outer-measure inequality. -/
theorem prod_compl_prod_le (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set α) (B : Set β) :
    (μ.prod ν) (A ×ˢ B)ᶜ ≤ μ Aᶜ + ν Bᶜ := by
  rw [Set.compl_prod_eq_union]
  simpa only [prod_prod, measure_univ, mul_one, one_mul] using
    measure_union_le (μ := μ.prod ν) (Aᶜ ×ˢ Set.univ) (Set.univ ×ˢ Bᶜ)

/-- At a binary merge, the true failure probability is at most the sum
of the two child failure probabilities and the uniform parent section
bound, which is required only on successful child pairs. -/
theorem prod_binary_failure_le_of_sections
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {A : Set α} {B : Set β} {E : Set ((α × β) × γ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (epsilon : ℝ≥0∞)
    (hsection : ∀ x ∈ A ×ˢ B, ρ (Prod.mk x ⁻¹' E) ≤ epsilon) :
    ((μ.prod ν).prod ρ) (Prod.fst ⁻¹' (A ×ˢ B)ᶜ ∪ E) ≤
      μ Aᶜ + ν Bᶜ + epsilon := by
  have hparent := prod_union_fst_compl_le_add_of_sections
    (μ.prod ν) ρ (hA.prod hB) hE epsilon hsection
  exact hparent.trans (add_le_add (prod_compl_prod_le μ ν A B) le_rfl)

end MeasureTheory.Measure
