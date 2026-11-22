/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.Measurable.MatrixFamilySupportMeasurable
import QICLean.Algebra.Hermitian.ProjectionMatrixRange

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

section FiniteFamilyImageCoordinates

/-!
# Finite operator-family images in prescribed Euclidean coordinates

The rectangular matrices of fixed operators after a fixed input isometry
represent exactly the common operator image of an arbitrary matrix range.
The joint column support is the existing support of that same family.
This supports ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
and the resampling description, lines 749–755.
-/

namespace Matrix

/-- The joint support of the actual rectangular operator matrices times an
arbitrary input matrix has exactly the common operator image of its range.
No projection or decomposition hypothesis is supplied. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 597–622. -/
theorem range_familySupportProj_comp_linearIsometryEquiv
    {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ] {d : ℕ}
    (I : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ σ)
    (A : ι → EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ σ)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    let F : ι → Matrix σ (Fin d) ℂ := fun i ↦
      (toEuclideanLin (m := σ) (n := Fin d) (𝕜 := ℂ)).symm
        ((A i).toLinearMap.comp I.toLinearMap)
    (toEuclideanLin (familySupportProj (fun i ↦ F i * P))).range =
      ⨆ i, ((toEuclideanLin P).range.map I.toLinearMap).map (A i).toLinearMap := by
  intro F
  rw [range_toEuclideanLin_familySupportProj]
  apply iSup_congr
  intro i
  have hmul : toEuclideanLin (F i * P) =
      (toEuclideanLin (F i)).comp (toEuclideanLin P) := toLpLin_mul_same 2 (F i) P
  rw [hmul]
  dsimp only [F]
  rw [LinearEquiv.apply_symm_apply, LinearMap.range_comp, Submodule.map_comp]

end Matrix

end FiniteFamilyImageCoordinates
