/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Analysis.IsometricDomainExtension
import QICLean.Algebra.MatrixSandwichIntertwine

/-!
# A norm comparison through an orthogonal projection

Let Z be a rectangular isometry, let A and N be Hermitian matrices, and let
P be an orthogonal projection. If (Z A Zᴴ) P = P N, taking adjoints reverses
the intertwining. Contractivity of P and norm preservation by Z then compare
the action of N on P u with the action of A on Zᴴ u.

Neither A nor N needs to be positive. The coordinate sets may be empty.
For the application to real powers of restricted replica metrics, A and N
are the corresponding positive matrix powers, and P is the actual symmetric
projection after insertion of a unit Bell vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308 and 370–381,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A Hermitian intertwining through an orthogonal projection and a rectangular
isometry gives a norm comparison. This is the finite-dimensional norm step for
the restricted powers in the area-law manuscript, `07-comparators.tex`,
lines 283–308 and 370–381. -/
theorem norm_projected_le_of_isometric_intertwine
    {A : Matrix n n ℂ} {N P : Matrix m m ℂ} {Z : Matrix m n ℂ}
    (hA : A.IsHermitian) (hN : N.IsHermitian) (hP : IsStarProjection P)
    (hZ : Zᴴ * Z = 1) (h : (Z * A * Zᴴ) * P = P * N)
    (u : EuclideanSpace ℂ m) :
    ‖toEuclideanLin N (toEuclideanLin P u)‖ ≤
      ‖toEuclideanLin A (toEuclideanLin Zᴴ u)‖ := by
  have hZnorm : ∀ v : EuclideanSpace ℂ n, ‖toEuclideanLin Z v‖ = ‖v‖ :=
    norm_toLp_mulVec_of_isometry Z hZ
  have hPadj : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
  have hreverse : N * P = P * (Z * A * Zᴴ) := by
    simpa only [hPadj] using
      (Matrix.isHermitian_mul_mul_conjTranspose Z hA).conjTranspose_intertwine hN P h
  calc
    ‖toEuclideanLin N (toEuclideanLin P u)‖ =
        ‖toEuclideanLin (N * P) u‖ := by
      simp only [toLpLin_mul_same, LinearMap.comp_apply]
    _ = ‖toEuclideanLin P
        (toEuclideanLin Z (toEuclideanLin A (toEuclideanLin Zᴴ u)))‖ := by
      rw [hreverse]
      simp only [toLpLin_mul_same, LinearMap.comp_apply]
    _ ≤ ‖P‖ * ‖toEuclideanLin Z (toEuclideanLin A (toEuclideanLin Zᴴ u))‖ :=
      P.l2_opNorm_mulVec _
    _ ≤ 1 * ‖toEuclideanLin Z (toEuclideanLin A (toEuclideanLin Zᴴ u))‖ :=
      mul_le_mul_of_nonneg_right (IsStarProjection.norm_le P hP) (norm_nonneg _)
    _ = ‖toEuclideanLin A (toEuclideanLin Zᴴ u)‖ := by
      rw [one_mul, hZnorm]

end Matrix
