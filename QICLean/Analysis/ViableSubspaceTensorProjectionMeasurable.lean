/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceProjectionEvent
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.MatrixTensorCoordinates

/-!
# True viability events in tensor projection coordinates

The actual projection of a tensor product of subspaces is represented by
the Kronecker product of their actual projection matrices in the fixed
product coordinates. This identifies Borel events for the original
viability predicate with the fixed target and its entire exterior space.
No gap, rank or nonempty-space hypothesis is needed.

Source: ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440, and
Lemma `l:t`, lines 500–523. These are geometric and measurability
auxiliaries, not an adaptive probability theorem.
-/

open MeasureTheory
open scoped TensorProduct Matrix.Norms.L2Operator Kronecker

namespace Submodule

variable {σ β : Type*} [Fintype σ] [Fintype β] [DecidableEq σ] [DecidableEq β]

/-- Relabeling coordinates relabels the actual subspace projection by
the same row and column equivalence. -/
theorem projectionMatrix_map_piLpCongrLeft (e : σ ≃ β)
    (S : Submodule ℂ (EuclideanSpace ℂ σ)) :
    (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ)).symm
      (S.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap).starProjection =
      ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm S.starProjection).reindex e e := by
  apply (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ)).symm_apply_eq.mpr
  apply ContinuousLinearMap.ext
  intro x
  rw [starProjection_map_apply]
  have h := congrArg (fun f ↦ f x)
    (Matrix.toEuclideanCLM_submatrix_intertwining e.symm
      ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm S.starProjection))
  have h' := congrArg (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e) h
  simp only [StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe''] at h'
  rw [← LinearIsometryEquiv.piLpCongrLeft_symm (p := 2) (𝕜 := ℂ) (E := ℂ) e] at h'
  simpa only [LinearIsometryEquiv.apply_symm_apply, Matrix.reindex_apply] using h'.symm

/-- A fixed finite relabeling preserves Borel dependence of the actual
orthogonal projection of a constructed subspace. -/
theorem measurable_projectionMatrix_map_piLpCongrLeft
    {X : Type*} [MeasurableSpace X] (e : σ ≃ β)
    (S : X → Submodule ℂ (EuclideanSpace ℂ σ))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm
      (S x).starProjection)) :
    Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ)).symm
      ((S x).map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap).starProjection) := by
  have hreindex : Continuous (fun P : Matrix σ σ ℂ ↦ P.reindex e e) := by
    change Continuous (fun P : Matrix σ σ ℂ ↦ fun i j ↦ P (e.symm i) (e.symm j))
    fun_prop
  simpa only [projectionMatrix_map_piLpCongrLeft, Function.comp_def] using
    hreindex.measurable.comp hS

/-- The actual tensor-product subspace has the Kronecker product of the
actual factor projections as its matrix in the fixed product coordinates. -/
theorem projectionMatrix_tensorProd_coordinates
    (S : Submodule ℂ (EuclideanSpace ℂ σ))
    (R : Submodule ℂ (EuclideanSpace ℂ β)) :
    (Matrix.toEuclideanCLM (n := σ × β) (𝕜 := ℂ)).symm
      ((S.tensorProd R).map (euclideanTensorEquiv σ β).symm.toLinearMap).starProjection =
      (Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm S.starProjection ⊗ₖ
        (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ)).symm R.starProjection := by
  apply (Matrix.toEuclideanCLM (n := σ × β) (𝕜 := ℂ)).symm_apply_eq.mpr
  apply ContinuousLinearMap.ext
  intro x
  rw [starProjection_map_apply, starProjection_tensorProd]
  have h := congrArg (fun f ↦ f (euclideanTensorEquiv σ β x))
    (Matrix.toEuclideanCLM_kronecker_intertwining
      ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm S.starProjection)
      ((Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ)).symm R.starProjection))
  simpa only [StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', euclideanTensorEquiv,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply] using h

/-- Borel actual factor projections give a Borel actual tensor-product
projection in the fixed product coordinates. -/
theorem measurable_projectionMatrix_tensorProd_coordinates
    {X : Type*} [MeasurableSpace X]
    (S : X → Submodule ℂ (EuclideanSpace ℂ σ))
    (R : X → Submodule ℂ (EuclideanSpace ℂ β))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm
      (S x).starProjection))
    (hR : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ)).symm
      (R x).starProjection)) :
    Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := σ × β) (𝕜 := ℂ)).symm
      (((S x).tensorProd (R x)).map
        (euclideanTensorEquiv σ β).symm.toLinearMap).starProjection) := by
  have hmul : Continuous (fun p : Matrix σ σ ℂ × Matrix β β ℂ ↦ p.1 ⊗ₖ p.2) := by
    unfold Matrix.kroneckerMap
    fun_prop
  simpa only [projectionMatrix_tensorProd_coordinates, Function.comp_def] using
    hmul.measurable.comp (hS.prodMk hR)

omit [DecidableEq β] in
/-- The original viability event is Borel for every fixed target in the
full local-space/exterior-space tensor product, whenever the constructed
local subspace has a Borel actual orthogonal projection. -/
theorem measurableSet_isViable_of_measurable_projectionMatrix
    {X : Type*} [MeasurableSpace X]
    (S : X → Submodule ℂ (EuclideanSpace ℂ σ))
    (hS : Measurable (fun x ↦ (Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm
      (S x).starProjection)) (delta : ℝ)
    (T : Submodule ℂ (EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)) :
    MeasurableSet {x : X | IsViable delta (S x) T} := by
  let : DecidableEq β := Classical.decEq β
  let U := fun x ↦ ((S x).tensorProd (⊤ : Submodule ℂ (EuclideanSpace ℂ β))).map
    (euclideanTensorEquiv σ β).symm.toLinearMap
  have hU := measurable_projectionMatrix_tensorProd_coordinates S
    (fun _ ↦ (⊤ : Submodule ℂ (EuclideanSpace ℂ β))) hS measurable_const
  have h := measurableSet_isCloseTo_of_measurable_projectionMatrix U hU delta
    (T.map (euclideanTensorEquiv σ β).symm.toLinearMap)
  convert h using 1
  ext x
  exact (isCloseTo_map_iff (euclideanTensorEquiv σ β).symm).symm

end Submodule
