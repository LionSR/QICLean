/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace
import QICLean.Analysis.ProjectionMatrixRange
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Closed tests for subspace closeness in projection coordinates

The actual subspace-closeness condition is a positive-semidefinite matrix
inequality in the candidate projection. Its success set is closed, so its
failure set is Borel measurable. This concerns the original predicate,
not an intermediate or chosen comparison subspace.

Source: ALVV, arXiv:1602.08828v2, Definition `d:close`, lines 469–474,
and Definition `d:vs`, lines 433–440.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- The compressed positive-semidefinite inequality is a closed condition
on the candidate matrix. The target matrix and error are fixed but otherwise
unrestricted. Auxiliary to ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474. -/
theorem isClosed_setOf_compressed_posSemidef {n : Type*} [Fintype n]
    (Q : Matrix n n ℂ) (delta : ℝ) :
    IsClosed {P : Matrix n n ℂ | (Q * P * Q - ((1 - delta : ℝ) : ℂ) • Q).PosSemidef} := by
  exact posSemidef_is_closed.preimage (by fun_prop)

end Matrix

namespace Submodule

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The original closeness predicate is exactly the compressed matrix
positivity test on the actual orthogonal projection matrices. Source: ALVV,
arXiv:1602.08828v2, Definition `d:close`, lines 469–474. -/
theorem isCloseTo_iff_compressed_posSemidef (delta : ℝ)
    (U T : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm U.starProjection
    let Q := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm T.starProjection
    IsCloseTo delta U T ↔ (Q * P * Q - ((1 - delta : ℝ) : ℂ) • Q).PosSemidef := by
  intro P Q
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  change IsCloseTo delta U T ↔
    ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (Q * P * Q - ((1 - delta : ℝ) : ℂ) • Q)).toLinearMap).IsPositive
  rw [ContinuousLinearMap.isPositive_toLinearMap_iff, map_sub, map_mul, map_mul, map_smul]
  simp only [P, Q, StarAlgEquiv.apply_symm_apply]
  exact ContinuousLinearMap.le_def

/-- The true subspace-closeness success set is closed on the space of
actual candidate orthogonal projection matrices. Its complement is
therefore Borel, including when a candidate has zero rank. No output
measurability premise is assumed. Source: ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474. -/
theorem isClosed_setOf_isCloseTo_projectionRange (delta : ℝ)
    (T : Submodule ℂ (EuclideanSpace ℂ n)) :
    IsClosed {P : {P : Matrix n n ℂ // IsStarProjection P} |
      IsCloseTo delta (LinearMap.range (Matrix.toEuclideanLin P.val)) T} := by
  let Q := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm T.starProjection
  have hset :
      {P : {P : Matrix n n ℂ // IsStarProjection P} |
        IsCloseTo delta (LinearMap.range (Matrix.toEuclideanLin P.val)) T} =
      Subtype.val ⁻¹' {P : Matrix n n ℂ |
        (Q * P * Q - ((1 - delta : ℝ) : ℂ) • Q).PosSemidef} := by
    ext P
    change IsCloseTo delta (LinearMap.range (Matrix.toEuclideanLin P.val)) T ↔
      (Q * P.val * Q - ((1 - delta : ℝ) : ℂ) • Q).PosSemidef
    simpa only [Matrix.projectionMatrix_range_of_isStarProjection, Q] using
      isCloseTo_iff_compressed_posSemidef delta
        (LinearMap.range (Matrix.toEuclideanLin P.val)) T
  rw [hset]
  exact (Matrix.isClosed_setOf_compressed_posSemidef Q delta).preimage continuous_subtype_val

end Submodule
