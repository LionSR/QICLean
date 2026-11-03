/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteFamilyImageProjection
import QICLean.Analysis.ViableSubspaceTensorProjectionMeasurable

/-!
# Borel orthogonal projections onto arbitrary matrix ranges

The actual orthogonal projection onto a matrix range is the existing joint
column support of its singleton family. Consequently it is Borel across
rank changes, without assuming that the matrix itself is a projection.
This supports true viability tests for the stopped sampling iteration in
ALVV, arXiv:1602.08828v2, the resampling description, lines 749–755.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The projection onto an arbitrary matrix range is the existing support
of the singleton matrix family, including zero and empty ranges. Used for
original-target viability in ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem projectionMatrix_range_eq_familySupportProj_singleton (P : Matrix m n ℂ) :
    (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm
      (toEuclideanLin P).range.starProjection = familySupportProj (fun _ : Fin 1 ↦ P) := by
  let Q := familySupportProj (fun _ : Fin 1 ↦ P)
  have hQ : IsStarProjection Q :=
    (familyColumnGram_posSemidef _).isHermitian.isStarProjection_supportProj
  have hrange : (toEuclideanLin Q).range = (toEuclideanLin P).range := by
    simpa only [iSup_const] using range_toEuclideanLin_familySupportProj (fun _ : Fin 1 ↦ P)
  have hp := projectionMatrix_range_of_isStarProjection ⟨Q, hQ⟩
  have heq := congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ m) ↦
    (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm S.starProjection) hrange
  exact heq.symm.trans hp

/-- The actual matrix of the orthogonal projection onto a rectangular
matrix range is globally Borel. No rank or projection premise is imposed.
Used for the stopped resampling iteration of ALVV, arXiv:1602.08828v2,
lines 749–755. -/
theorem measurable_projectionMatrix_range :
    Measurable (fun P : Matrix m n ℂ ↦ (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm
      (toEuclideanLin P).range.starProjection) := by
  have hsingleton : Continuous (fun P : Matrix m n ℂ ↦ fun _ : Fin 1 ↦ P) := by fun_prop
  simpa only [projectionMatrix_range_eq_familySupportProj_singleton, Function.comp_def] using
    (measurable_familySupportProj (ι := Fin 1) (m := m) (n := n)).comp hsingleton.measurable

end Matrix

namespace Submodule

/-- A Borel matrix family gives a Borel true viability event for its actual
range, in fixed native coordinates and against the whole exterior target.
No projection, rank or nonzero premise is imposed on the input matrices.
This supports ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem measurableSet_isCloseTo_prodExt_map_range
    {X σ β : Type*} [MeasurableSpace X]
    [Fintype σ] [Fintype β] {d : ℕ}
    (e : Fin d ≃ σ) (P : X → Matrix (Fin d) (Fin d) ℂ) (hP : Measurable P)
    (delta : ℝ) (Graw : Submodule ℂ (EuclideanSpace ℂ (σ × β))) :
    MeasurableSet {x | IsCloseTo delta
      (prodExt ((Matrix.toEuclideanLin (P x)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw} := by
  let : DecidableEq σ := Classical.decEq σ
  let : DecidableEq β := Classical.decEq β
  let W := fun x ↦ (Matrix.toEuclideanLin (P x)).range.map
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  have hRange : Measurable (fun x ↦
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (Matrix.toEuclideanLin (P x)).range.starProjection) :=
    (Matrix.measurable_projectionMatrix_range (m := Fin d) (n := Fin d)).comp hP
  have hW := measurable_projectionMatrix_map_piLpCongrLeft e
    (fun x ↦ (Matrix.toEuclideanLin (P x)).range) hRange
  have h := measurableSet_isViable_of_measurable_projectionMatrix W hW delta
    (Graw.map (euclideanTensorEquiv σ β).toLinearMap)
  convert h using 1
  ext x
  exact isCloseTo_prodExt_iff_isViable (δ := delta) (W x) Graw

end Submodule
