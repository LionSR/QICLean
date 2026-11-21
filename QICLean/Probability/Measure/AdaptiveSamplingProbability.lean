/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Section bounds for a fresh sampling variable

A uniform bound for a measurable failure section, conditional on a
measurable set of earlier histories, integrates to the same bound times
the measure of those histories. This is the measure-theoretic step used
to combine fixed-input sampling estimates in ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558, and the merge argument
at lines 1777–1817. Measurability of the actual parent construction is
proved separately before applying this estimate to an algorithm.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Integrating a uniform failure-section bound over good histories.
No jointly measurable choice of auxiliary success sets is required;
the measurable set here is the actual failure relation. -/
theorem prod_inter_fst_preimage_le_of_sections (μ : Measure α) (ν : Measure β)
    [SFinite ν] {A : Set α} {E : Set (α × β)} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (epsilon : ℝ≥0∞)
    (hsection : ∀ x ∈ A, ν (Prod.mk x ⁻¹' E) ≤ epsilon) :
    (μ.prod ν) (E ∩ Prod.fst ⁻¹' A) ≤ epsilon * μ A := by
  rw [prod_apply (hE.inter (hA.preimage measurable_fst))]
  refine (lintegral_mono (g := A.indicator (fun _ ↦ epsilon)) ?_).trans
    (lintegral_indicator_const hA epsilon).le
  intro x
  by_cases hx : x ∈ A
  · have hsub : Prod.mk x ⁻¹' (E ∩ Prod.fst ⁻¹' A) ⊆ Prod.mk x ⁻¹' E :=
      Set.preimage_mono Set.inter_subset_left
    simpa only [Set.indicator_of_mem hx] using (measure_mono hsub).trans (hsection x hx)
  · simp [Set.preimage, hx]

/-- Prior failure together with failure of a fresh sample has measure
at most the sum of the prior failure mass and its section bound. -/
theorem prod_union_fst_compl_le_of_sections (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure ν] {A : Set α} {E : Set (α × β)} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (epsilon : ℝ≥0∞)
    (hsection : ∀ x ∈ A, ν (Prod.mk x ⁻¹' E) ≤ epsilon) :
    (μ.prod ν) (Prod.fst ⁻¹' Aᶜ ∪ E) ≤ μ Aᶜ + epsilon * μ A := by
  have hguard := prod_inter_fst_preimage_le_of_sections μ ν hA hE epsilon hsection
  have hset : Prod.fst ⁻¹' Aᶜ ∪ E =
      Prod.fst ⁻¹' Aᶜ ∪ (E ∩ Prod.fst ⁻¹' A) := by
    rw [Set.union_inter_distrib_left, ← Set.preimage_union, Set.compl_union_self,
      Set.preimage_univ, Set.inter_univ]
  have hprior : (μ.prod ν) (Prod.fst ⁻¹' Aᶜ) = μ Aᶜ := by
    rw [← Set.prod_univ, prod_prod, measure_univ, mul_one]
  rw [hset]
  exact (measure_union_le _ _).trans (add_le_add hprior.le hguard)

/-- For probability histories and a fresh probability sample, the new
failure probability is at most the prior failure probability plus the
uniform conditional failure bound. -/
theorem prod_union_fst_compl_le_add_of_sections (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set α} {E : Set (α × β)} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (epsilon : ℝ≥0∞)
    (hsection : ∀ x ∈ A, ν (Prod.mk x ⁻¹' E) ≤ epsilon) :
    (μ.prod ν) (Prod.fst ⁻¹' Aᶜ ∪ E) ≤ μ Aᶜ + epsilon := by
  refine (prod_union_fst_compl_le_of_sections μ ν hA hE epsilon hsection).trans
    (add_le_add le_rfl ?_)
  simpa only [mul_one] using mul_le_mul_right (prob_le_one (μ := μ) (s := A)) epsilon

end MeasureTheory.Measure

section AdaptiveBinaryProbability

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

end AdaptiveBinaryProbability
