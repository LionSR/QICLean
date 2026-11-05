/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteFrameMeasurable
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Borel orthonormal frames for finite matrix ranges

The ordered frame of the actual column family spans the matrix range.
Its coordinates are Borel on each rank stratum, including rank zero. In
particular the construction applies to varying orthogonal projections;
no arbitrary orthonormal-basis choice is used. This is a prerequisite for
the varying input spaces in ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558,
rather than a joint adaptive sampling theorem.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {d r : ℕ}

private def euclideanColumns (A : Matrix (Fin d) (Fin d) ℂ) :
    Fin d → EuclideanSpace ℂ (Fin d) :=
  fun i ↦ toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A (EuclideanSpace.basisFun (Fin d) ℂ i)

private theorem span_euclideanColumns (A : Matrix (Fin d) (Fin d) ℂ) :
    Submodule.span ℂ (Set.range (euclideanColumns A)) = (toEuclideanLin A).range := by
  let b := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
  have hmap : (Submodule.span ℂ (Set.range b)).map (toEuclideanLin A) =
      Submodule.span ℂ (Set.range (fun i ↦ toEuclideanLin A (b i))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [b.span_eq, Submodule.map_top] at hmap
  exact hmap.symm

private theorem finrank_span_euclideanColumns (A : Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (euclideanColumns A))) = A.rank := by
  rw [span_euclideanColumns]
  rw [rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℂ).toBasis,
    toEuclideanLin_eq_toLin_orthonormal]

/-- The actual ordered orthonormal frame of a rank-r matrix range,
obtained by normalized Gram–Schmidt on its columns. -/
def rangeOrthonormalFrame (A : {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r}) :
    Fin r → EuclideanSpace ℂ (Fin d) :=
  InnerProductSpace.finiteOrthonormalFrame ℂ
    ⟨euclideanColumns A.val, (finrank_span_euclideanColumns A.val).trans A.property⟩

/-- The selected matrix-range frame is orthonormal, including rank zero. -/
theorem orthonormal_rangeOrthonormalFrame
    (A : {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r}) :
    Orthonormal ℂ (rangeOrthonormalFrame A) :=
  InnerProductSpace.orthonormal_finiteOrthonormalFrame ℂ _

/-- The actual selected frame spans the full matrix range. -/
theorem span_rangeOrthonormalFrame
    (A : {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r}) :
    Submodule.span ℂ (Set.range (rangeOrthonormalFrame A)) = (toEuclideanLin A.val).range :=
  (InnerProductSpace.span_finiteOrthonormalFrame ℂ _).trans (span_euclideanColumns A.val)

/-- The actual orthonormal frame is Borel on every finite-matrix rank
stratum. This applies in particular to all rank-r orthogonal projections. -/
theorem measurable_rangeOrthonormalFrame :
    Measurable (rangeOrthonormalFrame (d := d) (r := r)) := by
  have hcolumns : Measurable (euclideanColumns (d := d)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (continuous_uncurry_toEuclideanCLM.comp
      (continuous_id.prodMk continuous_const)).measurable
  have hmap : Measurable (fun A : {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r} ↦
      (⟨euclideanColumns A.val, (finrank_span_euclideanColumns A.val).trans A.property⟩ :
        {f : Fin d → EuclideanSpace ℂ (Fin d) //
          Module.finrank ℂ (Submodule.span ℂ (Set.range f)) = r})) :=
    (hcolumns.comp measurable_subtype_coe).subtype_mk
  exact (InnerProductSpace.measurable_finiteOrthonormalFrame ℂ).comp hmap

end Matrix
