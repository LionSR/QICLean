/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTensorProjectionMeasurable
import QICLean.Entropy.RegionalTensorMerge

/-!
# Borel projection of the actual regional tensor merge

The existing tensor merge of two disjoint physical regions has a Borel
actual orthogonal projection when its child projections are Borel. The
union coordinates are the original prescribed configuration equivalence.
Source: ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523.
This does not select an adaptive tree or assert its success probability.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator TensorProduct

namespace Entropy

/-- The existing regional tensor merge has a Borel actual orthogonal
projection as a function of constructed child spaces with Borel projections. -/
theorem measurable_projectionMatrix_regionTensorMerge
    {X V : Type*} [MeasurableSpace X] [DecidableEq V]
    (q : ℕ) (A B : Finset V) (h : Disjoint A B)
    (S1 : X → Submodule ℂ (EuclideanSpace ℂ (A → Fin q)))
    (S2 : X → Submodule ℂ (EuclideanSpace ℂ (B → Fin q)))
    (h1 : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := A → Fin q) (𝕜 := ℂ)).symm
      (S1 x).starProjection))
    (h2 : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := B → Fin q) (𝕜 := ℂ)).symm
      (S2 x).starProjection)) :
    Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := ↥(A ∪ B) → Fin q) (𝕜 := ℂ)).symm
      (regionTensorMerge q A B h (S1 x) (S2 x)).starProjection) := by
  let e := FiniteProduct.unionEquiv (fun _ : V ↦ Fin q) A B h
  let U := fun x ↦ ((S1 x).tensorProd (S2 x)).map
    (Submodule.euclideanTensorEquiv (A → Fin q) (B → Fin q)).symm.toLinearMap
  have hU := Submodule.measurable_projectionMatrix_tensorProd_coordinates S1 S2 h1 h2
  have hm := Submodule.measurable_projectionMatrix_map_piLpCongrLeft e.symm U hU
  have heq (x : X) : regionTensorMerge q A B h (S1 x) (S2 x) =
      (U x).map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearMap := by
    rw [← Submodule.map_comp]
    dsimp only [regionTensorMerge]
    congr 1
    dsimp only [unionTensorCoordinates]
    rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.piLpCongrLeft_symm]
    rfl
  simpa only [heq] using hm

end Entropy
