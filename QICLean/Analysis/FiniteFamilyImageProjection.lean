/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixFamilySupportMeasurable
import QICLean.Analysis.ProjectionMatrixRange

/-!
# The actual projection onto a finite family image

The existing joint column support represents the actual sum of operator
images in Euclidean coordinates. This identifies its Borel projector
with the ordinary subspace construction used by interleaved collective
trimming. Source: ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
and Figure `fig:merge-prime`, lines 1668–1670.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- The existing joint family support has exactly the sum of the actual
Euclidean matrix ranges, including empty and zero families. -/
theorem range_toEuclideanLin_familySupportProj
    {ι m n : Type*} [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : ι → Matrix m n ℂ) :
    LinearMap.range (toEuclideanLin (familySupportProj A)) =
      ⨆ i, LinearMap.range (toEuclideanLin (A i)) := by
  rw [range_toEuclideanLin_eq_map_range_mulVecLin,
    range_familySupportProj_eq_iSup_range, Submodule.map_iSup]
  simp_rw [range_toEuclideanLin_eq_map_range_mulVecLin]

/-- The actual orthogonal projection onto the sum of the operator images
is the existing family support applied to the operators times the actual
input projection. No rank or nonzero-space premise is required. -/
theorem projectionMatrix_iSup_map_eq_familySupportProj
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (F : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) :
    (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (⨆ i, S.map (F i).toLinearMap).starProjection =
      familySupportProj (fun i ↦ (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (F i) *
        (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm S.starProjection) := by
  let A := fun i ↦ (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (F i) *
    (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm S.starProjection
  have hrange : LinearMap.range (toEuclideanLin (familySupportProj A)) =
      ⨆ i, S.map (F i).toLinearMap := by
    rw [range_toEuclideanLin_familySupportProj]
    apply iSup_congr
    intro i
    change LinearMap.range ((toEuclideanCLM (n := n) (𝕜 := ℂ)) (A i)).toLinearMap = _
    dsimp only [A]
    rw [map_mul, StarAlgEquiv.apply_symm_apply, StarAlgEquiv.apply_symm_apply]
    change LinearMap.range ((F i).toLinearMap.comp S.starProjection.toLinearMap) = _
    rw [LinearMap.range_comp, Submodule.range_starProjection]
  have hP : IsStarProjection (familySupportProj A) :=
    (familyColumnGram_posSemidef A).isHermitian.isStarProjection_supportProj
  simpa only [hrange] using projectionMatrix_range_of_isStarProjection
    ⟨familySupportProj A, hP⟩

/-- The actual projection onto a fixed finite family's image of a
constructed subspace is Borel when its actual input projection is Borel. -/
theorem measurable_projectionMatrix_iSup_map
    {X ι n : Type*} [MeasurableSpace X] [Finite ι] [Fintype n] [DecidableEq n]
    (F : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (S : X → Submodule ℂ (EuclideanSpace ℂ n))
    (hS : Measurable (fun x ↦ (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (S x).starProjection)) :
    Measurable (fun x ↦ (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (⨆ i, (S x).map (F i).toLinearMap).starProjection) := by
  let : Fintype ι := Fintype.ofFinite ι
  simpa only [projectionMatrix_iSup_map_eq_familySupportProj, Function.comp_def] using
    (measurable_familySupportProj_mul
      (fun i ↦ (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (F i))).comp hS

end Matrix
