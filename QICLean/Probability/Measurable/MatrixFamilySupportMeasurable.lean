/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Support.MatrixFamilySupportProjection
import QICLean.Probability.Measurable.SpectralProjectionMeasurable
import QICLean.Algebra.Hermitian.ProjectionMatrixRange

/-!
# Measurable joint column supports

The existing joint column support of a finite matrix family is a Borel
function of that family. This gives the intrinsic projector for a finite
sum of operator images without selecting an orthonormal basis. It is an
auxiliary for the improving-family image in ALVV, arXiv:1602.08828v2,
Lemma `l:er`, lines 597–622. Adaptive probability is a separate argument.

## Main results

* `Matrix.projectionMatrix_span_range_eq_familySupportProj`,
  `Matrix.measurable_projectionMatrix_span_range`: the Borel projection onto the span of finite
  vectors.
-/

section MatrixFamilySupportMeasurable

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Matrix

variable {ι m n : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq ι] [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The existing joint column Gram matrix depends continuously on its
finite matrix family. -/
@[fun_prop]
theorem continuous_familyColumnGram :
    Continuous (familyColumnGram : (ι → Matrix m n ℂ) → Matrix m m ℂ) := by
  unfold familyColumnGram familyColumns
  fun_prop

omit [DecidableEq ι] [DecidableEq n] in
/-- The existing joint column support is recovered by the two closed
half-line cutoffs of its actual Gram matrix. -/
theorem familySupportProj_eq_one_sub_spectralProjectionGE_mul (A : ι → Matrix m n ℂ) :
    familySupportProj A = 1 - spectralProjectionGE (familyColumnGram A) 0 *
      spectralProjectionGE (-familyColumnGram A) 0 := by
  exact (familyColumnGram_posSemidef A).isHermitian.supportProj_eq_one_sub_spectralProjectionGE_mul

omit [DecidableEq ι] [DecidableEq n] in
/-- The existing joint column support is Borel measurable, including at
rank changes and for zero or empty families. -/
theorem measurable_familySupportProj :
    Measurable (familySupportProj : (ι → Matrix m n ℂ) → Matrix m m ℂ) := by
  let : DecidableEq ι := Classical.decEq ι
  let : DecidableEq n := Classical.decEq n
  have heq : (familySupportProj : (ι → Matrix m n ℂ) → Matrix m m ℂ) =
      (fun A ↦ 1 - spectralProjectionGE (familyColumnGram A) 0 *
        spectralProjectionGE (-familyColumnGram A) 0) := by
    funext A
    exact familySupportProj_eq_one_sub_spectralProjectionGE_mul A
  rw [heq]
  have hGram : Measurable (familyColumnGram : (ι → Matrix m n ℂ) → Matrix m m ℂ) :=
    (continuous_familyColumnGram (ι := ι) (m := m) (n := n)).measurable
  exact measurable_const.sub (((measurable_spectralProjectionGE 0).comp hGram).mul
    ((measurable_spectralProjectionGE 0).comp hGram.neg))


omit [DecidableEq ι] [DecidableEq n] in
/-- The existing joint support has exactly the range of the actual matrix
of all family columns. Empty and zero families are included. -/
theorem range_familySupportProj_eq_range_familyColumns (A : ι → Matrix m n ℂ) :
    LinearMap.range (familySupportProj A).mulVecLin =
      LinearMap.range (familyColumns A).mulVecLin := by
  have hAbsorb : familySupportProj A * familyColumns A = familyColumns A := by
    ext i p
    rcases p with ⟨a, j⟩
    simpa only [Matrix.mul_apply, familyColumns] using
      congrFun (congrFun (familySupportProj_mul A a) i) j
  apply le_antisymm
  · obtain ⟨T, hT⟩ := (familyColumnGram_posSemidef A).exists_supportProj_eq_mul
    have hfactor : familySupportProj A = familyColumns A * ((familyColumns A)ᴴ * T) := by
      change (familyColumnGram_posSemidef A).supportProj = _
      rw [hT, familyColumnGram, Matrix.mul_assoc]
    rw [hfactor, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range ((familyColumns A)ᴴ * T).mulVecLin
      (familyColumns A).mulVecLin
  · calc
      _ = LinearMap.range (familySupportProj A * familyColumns A).mulVecLin :=
        congrArg (fun C ↦ LinearMap.range C.mulVecLin) hAbsorb.symm
      _ ≤ _ := by
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range (familyColumns A).mulVecLin
          (familySupportProj A).mulVecLin

omit [DecidableEq ι] [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The columns of the actual stacked family span the sum of the actual
ranges of the family members. -/
theorem range_familyColumns_eq_iSup_range (A : ι → Matrix m n ℂ) :
    LinearMap.range (familyColumns A).mulVecLin =
      ⨆ a, LinearMap.range (A a).mulVecLin := by
  simp_rw [Matrix.range_mulVecLin]
  change Submodule.span ℂ (Set.range (Function.uncurry fun a j ↦ (A a).col j)) = _
  have heq : Set.range (Function.uncurry fun a j ↦ (A a).col j) =
      ⋃ a, Set.range (A a).col := by
    ext v
    simp only [Set.mem_range, Set.mem_iUnion, Prod.exists]
    rfl
  rw [heq, Submodule.span_iUnion]

omit [DecidableEq ι] [DecidableEq n] in
/-- The existing joint column support represents exactly the sum of all
actual family-image spaces. No rank or nonzero-family hypothesis is used. -/
theorem range_familySupportProj_eq_iSup_range (A : ι → Matrix m n ℂ) :
    LinearMap.range (familySupportProj A).mulVecLin =
      ⨆ a, LinearMap.range (A a).mulVecLin :=
  (range_familySupportProj_eq_range_familyColumns A).trans (range_familyColumns_eq_iSup_range A)


omit [DecidableEq ι] [DecidableEq n] in
/-- For a fixed operator family, the existing support of its products
with an input matrix is Borel in that input matrix. -/
theorem measurable_familySupportProj_mul (F : ι → Matrix m n ℂ) :
    Measurable (fun P : Matrix n n ℂ ↦ familySupportProj (fun i ↦ F i * P)) := by
  let : DecidableEq ι := Classical.decEq ι
  let : DecidableEq n := Classical.decEq n
  have hfamily : Continuous (fun P : Matrix n n ℂ ↦ fun i ↦ F i * P) := by fun_prop
  exact measurable_familySupportProj.comp hfamily.measurable

omit [DecidableEq ι] [DecidableEq n] in
/-- The same existing support of the products represents precisely the
sum of the actual operator images of the input range. In particular an
input orthogonal projection represents its original subspace. -/
theorem range_familySupportProj_mul_eq_iSup_map_range
    (F : ι → Matrix m n ℂ) (P : Matrix n n ℂ) :
    LinearMap.range (familySupportProj (fun i ↦ F i * P)).mulVecLin =
      ⨆ i, (LinearMap.range P.mulVecLin).map (F i).mulVecLin := by
  simpa only [Matrix.mulVecLin_mul, LinearMap.range_comp] using
    range_familySupportProj_eq_iSup_range (fun i ↦ F i * P)

end Matrix

end MatrixFamilySupportMeasurable

section FiniteSpanProjectionMeasurable

/-!
## The Borel projection onto the span of finite vectors

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

end FiniteSpanProjectionMeasurable
