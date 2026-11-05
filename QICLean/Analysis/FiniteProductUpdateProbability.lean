/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteProductSectionProbability

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
