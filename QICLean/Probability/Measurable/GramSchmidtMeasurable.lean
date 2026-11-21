/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

/-!
# Borel Gram–Schmidt maps on arbitrary finite families

The existing Gram–Schmidt process and its normalized version are measurable
on all finite vector families in a separable real or complex inner product
space. Linear independence is not assumed: dependent directions give zero
vectors, and the normalized process retains zero there by the convention
that the inverse of zero is zero.

These are mathematical prerequisites for choosing measurable orthonormal
frames in the sampling step of ALVV, arXiv:1602.08828v2, `l:rs`, lines
530–558. They neither select a varying frame nor construct an adaptive law.
-/

open MeasureTheory

namespace InnerProductSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {n : ℕ}

private theorem measurable_gramSchmidt_apply (i : Fin n) :
    Measurable (fun f : Fin n → E ↦ gramSchmidt 𝕜 f i) := by
  classical
  have heq : (fun f : Fin n → E ↦ gramSchmidt 𝕜 f i) =
      (fun f ↦ f i - ∑ j ∈ Finset.Iio i, (𝕜 ∙ gramSchmidt 𝕜 f j).starProjection (f i)) := by
    funext f
    exact gramSchmidt_def 𝕜 f i
  rw [heq]
  simp only [Submodule.starProjection_singleton]
  apply (measurable_pi_apply i).sub
  apply Finset.measurable_sum
  intro j hj
  have hprev := measurable_gramSchmidt_apply j
  exact ((hprev.inner (measurable_pi_apply i)).div
    (RCLike.measurable_ofReal.comp (hprev.norm.pow_const 2))).smul hprev
termination_by i
decreasing_by exact (show j < i from Finset.mem_Iio.mp hj)

/-- The existing Gram–Schmidt transformation is Borel on every finite
family, including dependent families. No zero vector is discarded. -/
theorem measurable_gramSchmidt :
    Measurable (fun f : Fin n → E ↦ gramSchmidt 𝕜 f) :=
  measurable_pi_iff.mpr fun i ↦ measurable_gramSchmidt_apply 𝕜 i

/-- The existing normalized Gram–Schmidt transformation is Borel on every
finite family. It keeps zero vectors equal to zero, so no independence or
nonvanishing hypothesis is required. -/
theorem measurable_gramSchmidtNormed :
    Measurable (fun f : Fin n → E ↦ gramSchmidtNormed 𝕜 f) := by
  apply measurable_pi_iff.mpr
  intro i
  have hprev := (measurable_pi_apply i).comp (measurable_gramSchmidt 𝕜 (E := E))
  exact (RCLike.measurable_ofReal.comp hprev.norm).inv.smul hprev

end InnerProductSpace
