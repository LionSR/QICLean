/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteFamilyImageProjection

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
