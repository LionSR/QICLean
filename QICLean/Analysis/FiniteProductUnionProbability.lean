/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteProductUpdateProbability

/-!
# A finite list of failures in independent coordinates

Uniform bounds on the true one-coordinate sections of listed measurable
failure events give their union a bound proportional to the list length.
Repeated labels are permitted. The coordinate index and the event labels
need not coincide. This is an auxiliary to the finite merge analysis of
ALVV, arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- A finite list of measurable failure events has union measure at most
its length times a common bound on their true update sections. Repeated
labels are allowed, and an empty label type causes no exception.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1` and
lines 1777–1817. -/
theorem pi_biUnion_list_le_of_update_sections
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (l : List κ) (coordinate : κ → ι) (E : κ → Set (∀ j, α j)) (beta : ℝ≥0∞)
    (hE : ∀ a ∈ l, MeasurableSet (E a))
    (hsection : ∀ a ∈ l, ∀ ω : ∀ j, α j,
      μ (coordinate a) {u | Function.update ω (coordinate a) u ∈ E a} ≤ beta) :
    Measure.pi μ (⋃ a ∈ l, E a) ≤ (l.length : ℝ≥0∞) * beta := by
  revert hE hsection
  induction l with
  | nil =>
    intro _ _
    simp
  | cons a l ih =>
    intro hE hsection
    have hhead := pi_le_of_update_sections μ (coordinate a)
      (hE a List.mem_cons_self) beta (hsection a List.mem_cons_self)
    have htail := ih
      (fun b hb ↦ hE b (List.mem_cons_of_mem a hb))
      (fun b hb ↦ hsection b (List.mem_cons_of_mem a hb))
    calc
      Measure.pi μ (⋃ b ∈ a :: l, E b) =
          Measure.pi μ (E a ∪ ⋃ b ∈ l, E b) := by
        simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]
      _ ≤ Measure.pi μ (E a) + Measure.pi μ (⋃ b ∈ l, E b) := measure_union_le _ _
      _ ≤ beta + (l.length : ℝ≥0∞) * beta := add_le_add hhead htail
      _ = ((a :: l).length : ℝ≥0∞) * beta := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

end MeasureTheory.Measure
