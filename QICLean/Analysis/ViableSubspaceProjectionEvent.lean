/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceMeasurable

/-!
# Borel closeness events for constructed subspaces

A Borel actual orthogonal projection gives a Borel event for the original
subspace-closeness predicate. This is a direct pullback of the closed test,
not an assumption that the success event is measurable. Source: ALVV,
arXiv:1602.08828v2, Definition `d:close`, lines 469–474.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace Submodule

/-- A constructed subspace with Borel actual orthogonal projection has
a Borel true-closeness event for every fixed target and error. -/
theorem measurableSet_isCloseTo_of_measurable_projectionMatrix
    {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
    (S : X → Submodule ℂ (EuclideanSpace ℂ n))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (S x).starProjection)) (delta : ℝ) (T : Submodule ℂ (EuclideanSpace ℂ n)) :
    MeasurableSet {x : X | IsCloseTo delta (S x) T} := by
  let P := fun x ↦ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (S x).starProjection
  have hP (x : X) : IsStarProjection (P x) :=
    isStarProjection_starProjection.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
  have hm : Measurable (fun x ↦ (⟨P x, hP x⟩ :
      {P : Matrix n n ℂ // IsStarProjection P})) := hS.subtype_mk
  have hrange (x : X) : LinearMap.range (Matrix.toEuclideanLin (P x)) = S x := by
    change LinearMap.range
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (P x)).toLinearMap = S x
    rw [StarAlgEquiv.apply_symm_apply]
    exact range_starProjection _
  have h := (isClosed_setOf_isCloseTo_projectionRange delta T).measurableSet.preimage hm
  change MeasurableSet {x : X | IsCloseTo delta (Matrix.toEuclideanLin (P x)).range T} at h
  simpa only [hrange] using h

end Submodule
