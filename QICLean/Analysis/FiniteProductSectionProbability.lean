/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.AdaptiveSamplingProbability
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
