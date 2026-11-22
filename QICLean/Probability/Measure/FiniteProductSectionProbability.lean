/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.Measure.AdaptiveSamplingProbability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Failure sections in a finite independent product

A measurable failure event has probability at most epsilon when every
section in one independent coordinate does. The other coordinates may
include every earlier and later random choice. This permits local guarded
failures in the actual ALVV hierarchy to be integrated before summing over
its internal intervals. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- A uniform failure bound along one coordinate of a finite probability
product bounds the probability of the actual measurable event. The
sections use the canonical coordinate insertion, without an independence
hypothesis on the event itself. -/
theorem pi_le_of_coordinate_sections {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1))
    {E : Set (∀ j, α j)} (hE : MeasurableSet E) (epsilon : ℝ≥0∞)
    (hsection : ∀ x : (j : Fin n) → α (i.succAbove j),
      μ i {u | (MeasurableEquiv.piFinSuccAbove α i).symm (u, x) ∈ E} ≤ epsilon) :
    Measure.pi μ E ≤ epsilon := by
  let e := (MeasurableEquiv.piFinSuccAbove α i).trans MeasurableEquiv.prodComm
  have hpres : MeasurePreserving e (Measure.pi μ)
      ((Measure.pi fun j ↦ μ (i.succAbove j)).prod (μ i)) :=
    measurePreserving_swap.comp (measurePreserving_piFinSuccAbove μ i)
  have hbound := prod_inter_fst_preimage_le_of_sections
    (Measure.pi fun j : Fin n ↦ μ (i.succAbove j)) (μ i)
    (A := Set.univ) (E := e.symm ⁻¹' E) MeasurableSet.univ
    (hE.preimage e.symm.measurable) epsilon (fun x _ ↦ hsection x)
  simpa only [Set.preimage_univ, Set.inter_univ, measure_univ, mul_one,
    (hpres.symm e).measure_preimage_equiv E] using hbound

end MeasureTheory.Measure

section FiniteProductUpdateProbability

/-!
# Uniform update sections in a finite probability product

A measurable event in a finite independent product has measure at most
its uniform one-coordinate section bound. The index may be any finite
set, including the endpoint pairs of a chain. The sections are expressed
by replacing one coordinate in a whole seed. Nonemptiness of the
coordinate spaces follows from their probability measures.

This supports the probability analysis of ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817. It introduces no new sampling law
and assumes no probability bound on the full event.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Uniform bounds on the sections obtained by replacing one coordinate
bound the measure of an actual measurable event in any finite probability
product. The coordinate laws themselves imply nonemptiness; no separate
nonemptiness assumption on their spaces is needed. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817. -/
theorem pi_le_of_update_sections {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    {E : Set (∀ j, α j)} (hE : MeasurableSet E) (epsilon : ℝ≥0∞)
    (hsection : ∀ ω : ∀ j, α j,
      μ i {u | Function.update ω i u ∈ E} ≤ epsilon) :
    Measure.pi μ E ≤ epsilon := by
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin ι
  rcases n with _ | n
  · exact Fin.elim0 (f i)
  let e := f.symm
  obtain ⟨j, rfl⟩ := e.surjective i
  let q := MeasurableEquiv.piCongrLeft α e
  have hpres : MeasurePreserving q (Measure.pi fun k ↦ μ (e k)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hupdate (ω : (k : Fin (n + 1)) → α (e k)) (u : α (e j)) :
      q (Function.update ω j u) = Function.update (q ω) (e j) u := by
    ext k
    obtain ⟨k, rfl⟩ := e.surjective k
    by_cases hk : k = j
    · subst k
      simp only [q, MeasurableEquiv.piCongrLeft_apply_apply, Function.update_self]
    · simp only [q, MeasurableEquiv.piCongrLeft_apply_apply,
        Function.update_of_ne hk, Function.update_of_ne (e.injective.ne hk)]
  have hbound := pi_le_of_coordinate_sections (fun k : Fin (n + 1) ↦ μ (e k)) j
    (hE.preimage q.measurable) epsilon (fun x ↦ ?_)
  · simpa only [hpres.measure_preimage_equiv E] using hbound
  obtain ⟨u0⟩ := nonempty_of_isProbabilityMeasure (μ (e j))
  have hinsert (u : α (e j)) :
      q ((MeasurableEquiv.piFinSuccAbove (fun k ↦ α (e k)) j).symm (u, x)) =
        Function.update (q (j.insertNth u0 x)) (e j) u := by
    change q (j.insertNth u x) = _
    rw [← Fin.update_insertNth (α := fun k : Fin (n + 1) ↦ α (e k)) j u0 u x, hupdate]
  simpa only [Set.mem_preimage, hinsert] using hsection (q (j.insertNth u0 x))

end MeasureTheory.Measure

end FiniteProductUpdateProbability

section FiniteProductUnionProbability

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

end FiniteProductUnionProbability
