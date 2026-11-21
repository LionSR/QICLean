/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Projection matrices and ranges in Euclidean coordinates

An orthogonal projection matrix is the matrix of the orthogonal projection
onto its actual range. Rectangular ranges are transported from ordinary
function coordinates to Euclidean coordinates by the existing linear
equivalence. These identities support ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474, and collective trimming,
Definition `def:trimming`, lines 648–655.
-/

namespace Matrix

/-- The existing Euclidean coordinate equivalence transports the ordinary
matrix range exactly to the Euclidean matrix range. Used for collective
trimming in ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem range_toEuclideanLin_eq_map_range_mulVecLin {m n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    LinearMap.range (toEuclideanLin A) =
      (LinearMap.range A.mulVecLin).map
        (WithLp.linearEquiv 2 ℂ (m → ℂ)).symm.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨A *ᵥ WithLp.ofLp y, ⟨WithLp.ofLp y, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨WithLp.toLp 2 z, rfl⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of the orthogonal projection onto the range of an actual
orthogonal projection matrix is that same matrix. Extracted unchanged
from the closeness event proof; used in ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474. -/
theorem projectionMatrix_range_of_isStarProjection
    (P : {P : Matrix n n ℂ // IsStarProjection P}) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (LinearMap.range (Matrix.toEuclideanLin P.val)).starProjection = P.val := by
  obtain ⟨_, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp
    (P.property.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)))
  exact (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm_apply_eq.mpr heq.symm


end Matrix
