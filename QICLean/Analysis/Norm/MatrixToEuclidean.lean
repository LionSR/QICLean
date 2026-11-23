/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

/-!
# Complex matrices acting on Euclidean space

Coordinate facts about the linear and continuous linear maps of a complex matrix on Euclidean
space: the inner product `⟪x, A y⟫` is the dot product `star x ⬝ᵥ A y` of coordinate vectors,
a matrix of operator norm at most one does not increase the norm of a vector, the identity
matrix acts as the identity, a product acts as the composition, the matrix of a linear map has
the coordinates of the images of the basis vectors as columns and the operator norm of the map,
and the maps of two matrices are in Loewner order exactly when the matrices are. Mathlib states
the first only over the reals (`Matrix.inner_toEuclideanCLM`).

## Main results

* `Matrix.inner_toEuclideanCLM_eq_dotProduct`: `⟪x, A y⟫ = star x ⬝ᵥ (A *ᵥ y)`.
* `Matrix.norm_toEuclideanCLM_le_of_norm_le_one`: `‖A‖ ≤ 1` gives `‖A x‖ ≤ ‖x‖`.
* `Matrix.toEuclideanLin_one_apply`, `Matrix.toEuclideanLin_mul_apply`,
  `Matrix.toEuclideanLin_single_one_apply`.
* `Matrix.toEuclideanLin_symm_apply`, `Matrix.l2_opNorm_toEuclideanLin_symm`: the entries and
  the operator norm of the matrix of a linear map of Euclidean spaces.
* `Matrix.toEuclideanLin_le_toEuclideanLin_iff`, `Matrix.toEuclideanCLM_le_toEuclideanCLM_iff`:
  the maps on Euclidean space are in Loewner order exactly when the matrices are.

Moved from TNLean, `TNLean/Algebra/ToEuclideanCLM.lean` and
`TNLean/Algebra/ToEuclideanLinApply.lean` at commit `49b78ed821` (Apache-2.0).
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The expectation `⟪x, A y⟫` as a dot product of coordinate vectors. -/
theorem inner_toEuclideanCLM_eq_dotProduct (A : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) A y⟫_ℂ = star x.ofLp ⬝ᵥ (A *ᵥ y.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM, dotProduct_comm]

/-- A contraction does not increase the norm of a vector. -/
theorem norm_toEuclideanCLM_le_of_norm_le_one {A : Matrix n n ℂ} (hA1 : ‖A‖ ≤ 1)
    (x : EuclideanSpace ℂ n) : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_of_opNorm_le hA1 x

/-- The identity matrix acts as the identity. -/
theorem toEuclideanLin_one_apply {m : Type*} [Fintype m] [DecidableEq m]
    (x : EuclideanSpace ℂ m) : toEuclideanLin (1 : Matrix m m ℂ) x = x := by
  ext i
  simp

/-- Applying a product of matrices is the composition of the applications. -/
theorem toEuclideanLin_mul_apply {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (x : EuclideanSpace ℂ m) :
    toEuclideanLin (A * B) x = toEuclideanLin A (toEuclideanLin B x) := by
  ext i
  simp [toLpLin_apply, mulVec_mulVec]

/-- The column of a matrix at the basis vector `|z⟩` has the entries `σ x z`. -/
theorem toEuclideanLin_single_one_apply {l m : Type*} [Fintype m] [DecidableEq m]
    (σ : Matrix l m ℂ) (z : m) (x : l) :
    toEuclideanLin σ (EuclideanSpace.single z 1) x = σ x z := by
  simp [toLpLin_apply]

/-- The entry `(i, j)` of the matrix of a linear map of Euclidean spaces is the coordinate `i`
of the image of the basis vector `j`. -/
theorem toEuclideanLin_symm_apply {l m : Type*} [Fintype m] [DecidableEq m]
    (T : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ l) (i : l) (j : m) :
    (toEuclideanLin (𝕜 := ℂ)).symm T i j = T (EuclideanSpace.single j 1) i := by
  simp [toLpLin]

/-- The matrix of a continuous linear map of Euclidean spaces has the same operator norm. -/
theorem l2_opNorm_toEuclideanLin_symm {l m : Type*} [Fintype l] [Fintype m] [DecidableEq m]
    (T : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ l) :
    ‖(toEuclideanLin (𝕜 := ℂ)).symm T.toLinearMap‖ = ‖T‖ := by
  rw [l2_opNorm_def]
  congr 1
  ext1 x
  simp

open scoped MatrixOrder ComplexOrder

/-- The linear maps of two matrices on Euclidean space are in Loewner order exactly when the
matrices are: `A ≤ B` means that `B - A` is positive semidefinite. -/
theorem toEuclideanLin_le_toEuclideanLin_iff {A B : Matrix n n ℂ} :
    toEuclideanLin A ≤ toEuclideanLin B ↔ A ≤ B := by
  rw [LinearMap.le_def, ← map_sub, isPositive_toEuclideanLin_iff, Matrix.le_iff]

/-- The continuous linear maps of two matrices on Euclidean space are in Loewner order exactly
when the matrices are. -/
theorem toEuclideanCLM_le_toEuclideanCLM_iff {A B : Matrix n n ℂ} :
    toEuclideanCLM (n := n) (𝕜 := ℂ) A ≤ toEuclideanCLM (n := n) (𝕜 := ℂ) B ↔ A ≤ B := by
  rw [← ContinuousLinearMap.coe_le_coe_iff, coe_toEuclideanCLM_eq_toEuclideanLin,
    coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_le_toEuclideanLin_iff]

end Matrix
