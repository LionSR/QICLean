/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixFamilySupportMeasurable
import QICLean.Analysis.ProjectionMatrixRange

/-!
# The Borel projection onto the span of finite vectors

The existing joint-column support of the vectors as one-column matrices
is exactly the orthogonal projection onto their actual span. This gives
Borel dependence without any rank or independence assumption.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
-/

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]

private theorem range_support_columns_eq_span (u : ι → EuclideanSpace ℂ m) :
    LinearMap.range (toEuclideanLin (familySupportProj
      (fun i ↦ replicateCol Unit (WithLp.ofLp (u i))))) = Submodule.span ℂ (Set.range u) := by
  rw [range_toEuclideanLin_eq_map_range_mulVecLin,
    range_familySupportProj_eq_range_familyColumns, range_mulVecLin,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i, ⟨⟩⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i, ()), rfl⟩

/-- The matrix of the orthogonal projection onto the actual span of a
finite vector family is the existing support of its one-column matrices.
Zero vectors, dependencies and empty families are included. Used for ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem projectionMatrix_span_range_eq_familySupportProj
    (u : ι → EuclideanSpace ℂ m) :
    (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm
      (Submodule.span ℂ (Set.range u)).starProjection =
      familySupportProj (fun i ↦ replicateCol Unit (WithLp.ofLp (u i))) := by
  have hP : IsStarProjection (familySupportProj
      (fun i ↦ replicateCol Unit (WithLp.ofLp (u i)))) :=
    (familyColumnGram_posSemidef _).isHermitian.isStarProjection_supportProj
  have h := projectionMatrix_range_of_isStarProjection
    ⟨familySupportProj (fun i ↦ replicateCol Unit (WithLp.ofLp (u i))), hP⟩
  have hspan := congrArg
    (fun S : Submodule ℂ (EuclideanSpace ℂ m) ↦
      (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm S.starProjection)
    (range_support_columns_eq_span u)
  exact hspan.symm.trans h

omit [Fintype ι] in
/-- The actual orthogonal projection onto the span of an arbitrary finite
vector family is globally Borel measurable in that family, including at
rank changes. No basis, independence or nonzero premise is supplied.
Used for ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem measurable_projectionMatrix_span_range [Finite ι] :
    Measurable (fun u : ι → EuclideanSpace ℂ m ↦
      (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm
        (Submodule.span ℂ (Set.range u)).starProjection) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hcolumns : Continuous (fun u : ι → EuclideanSpace ℂ m ↦
      fun i ↦ replicateCol Unit (WithLp.ofLp (u i))) := by
    unfold replicateCol
    fun_prop
  simpa only [projectionMatrix_span_range_eq_familySupportProj, Function.comp_def] using
    (measurable_familySupportProj (ι := ι) (m := m) (n := Unit)).comp hcolumns.measurable

end Matrix
