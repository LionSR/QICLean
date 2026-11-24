/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import QICLean.Analysis.Norm.MatrixKroneckerContraction

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

The last section states the action of rectangular matrices: the bound by the operator norm,
equal lengths for equal Gram matrices `Aᴴ A`, relabelled rows, the defect `‖M ψ - ψ‖` of a
product of contractions, a Kronecker product on a product vector and a permutation matrix on a
basis vector.
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
theorem toEuclideanLin_mul_apply {l m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix l m ℂ) (B : Matrix m k ℂ) (x : EuclideanSpace ℂ k) :
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

/-!
### Rectangular matrices acting on Euclidean vectors

A complex matrix `A` with rows `m` and columns `n` acts on `EuclideanSpace ℂ n` by
`Matrix.toEuclideanLin A`. The facts below are stated for rectangular matrices: applying two
matrices in turn is applying their product, the action is bounded by the operator norm, two
matrices with the same Gram matrix `Aᴴ A` move every vector to the same length, relabelling the
rows does not change lengths, the defect `‖M ψ - ψ‖` does not depend on the coordinates, a
product of contractions has defect at most the sum of the defects, a Kronecker product acts
factorwise on a product vector, and a permutation matrix moves standard basis vectors. Two
facts on unit coordinate vectors close the section.
-/

open scoped Kronecker

namespace Matrix

section Rectangular

variable {m m' n : Type*} [Fintype n] [DecidableEq n]

variable [Fintype m]

/-- A matrix bounds its action on a vector by its operator norm. -/
theorem norm_toEuclideanLin_apply_le (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ :=
  (toEuclideanLin.trans LinearMap.toContinuousLinearMap A).le_opNorm x

/-- A matrix of operator norm at most one does not increase the norm of a vector. -/
theorem norm_toEuclideanLin_apply_le_of_norm_le_one {A : Matrix m n ℂ} (hA : ‖A‖ ≤ 1)
    (x : EuclideanSpace ℂ n) : ‖toEuclideanLin A x‖ ≤ ‖x‖ :=
  (norm_toEuclideanLin_apply_le A x).trans (mul_le_of_le_one_left (norm_nonneg _) hA)

omit [Fintype m] in
/-- The squared norm of `A x` is the expectation of the Gram matrix `Aᴴ A` in `x`. -/
private theorem norm_toEuclideanLin_apply_sq [Fintype m] (A : Matrix m n ℂ)
    (x : EuclideanSpace ℂ n) :
    ((‖toEuclideanLin A x‖ : ℂ) ^ 2) = star x.ofLp ⬝ᵥ ((Aᴴ * A) *ᵥ x.ofLp) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (toEuclideanLin A x)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, dotProduct_comm]
  exact_mod_cast h.symm

/-- Two matrices with the same Gram matrix move every vector to the same length. -/
theorem norm_toEuclideanLin_apply_eq_of_conjTranspose_mul_eq [Fintype m'] {A : Matrix m n ℂ}
    {B : Matrix m' n ℂ} (h : Aᴴ * A = Bᴴ * B) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin A x‖ = ‖toEuclideanLin B x‖ := by
  have h2 : ((‖toEuclideanLin A x‖ : ℂ) ^ 2) = ((‖toEuclideanLin B x‖ : ℂ) ^ 2) := by
    rw [norm_toEuclideanLin_apply_sq, norm_toEuclideanLin_apply_sq, h]
  have h3 : ‖toEuclideanLin A x‖ ^ 2 = ‖toEuclideanLin B x‖ ^ 2 := by exact_mod_cast h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- Relabelling the rows of a matrix along an equivalence does not change the norm of its
action on a vector. -/
theorem norm_toEuclideanLin_submatrix_apply [Fintype m'] (A : Matrix m n ℂ) (e : m' ≃ m)
    (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin (A.submatrix e id) x‖ = ‖toEuclideanLin A x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact e.sum_comp fun i ↦ ‖toEuclideanLin A x i‖ ^ 2

omit [Fintype m] in
/-- The defect `‖(M - 1) ψ‖` of a square matrix does not depend on the coordinates: relabelling
the basis along `e` relabels the vector. -/
theorem norm_toEuclideanLin_submatrix_apply_sub [Fintype m] [DecidableEq m] (M : Matrix n n ℂ)
    (e : m ≃ n) (ψ : EuclideanSpace ℂ m) :
    ‖toEuclideanLin (M.submatrix e e) ψ - ψ‖ =
      ‖toEuclideanLin M (WithLp.toLp 2 (ψ.ofLp ∘ e.symm)) - WithLp.toLp 2 (ψ.ofLp ∘ e.symm)‖ := by
  have h : toEuclideanLin (M.submatrix e e) ψ - ψ =
      WithLp.toLp 2 ((M *ᵥ (ψ.ofLp ∘ e.symm) - ψ.ofLp ∘ e.symm) ∘ e) := by
    ext x
    simp [toLpLin_apply, submatrix_mulVec_equiv]
  rw [h, EuclideanSpace.norm_toLp_comp_equiv]
  rfl

omit [Fintype m] in
/-- **Telescoping on a vector.** For contractions `A₁, …, A_s`, the defect of their product on
`ψ` is at most the sum of their individual defects on `ψ`. -/
theorem norm_toEuclideanLin_list_prod_sub_le :
    (L : List (Matrix n n ℂ)) → (∀ A ∈ L, ‖A‖ ≤ 1) → (ψ : EuclideanSpace ℂ n) →
      ‖toEuclideanLin L.prod ψ - ψ‖ ≤ (L.map fun A ↦ ‖toEuclideanLin A ψ - ψ‖).sum
  | [], _, ψ => by simp
  | A :: L, h, ψ => by
    rw [List.prod_cons, List.map_cons, List.sum_cons, toEuclideanLin_mul_apply]
    have hA := h A List.mem_cons_self
    have ih := norm_toEuclideanLin_list_prod_sub_le L
      (fun B hB ↦ h B (List.mem_cons_of_mem _ hB)) ψ
    calc ‖toEuclideanLin A (toEuclideanLin L.prod ψ) - ψ‖
        = ‖toEuclideanLin A (toEuclideanLin L.prod ψ - ψ) + (toEuclideanLin A ψ - ψ)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖toEuclideanLin A (toEuclideanLin L.prod ψ - ψ)‖ + ‖toEuclideanLin A ψ - ψ‖ :=
          norm_add_le _ _
      _ ≤ ‖toEuclideanLin L.prod ψ - ψ‖ + ‖toEuclideanLin A ψ - ψ‖ :=
          add_le_add (norm_toEuclideanLin_apply_le_of_norm_le_one hA _) le_rfl
      _ ≤ _ := by linarith

end Rectangular

/-- A Kronecker product acts factorwise on a product vector: `(A ⊗ B)(x ⊗ y) = (A x) ⊗ (B y)`. -/
theorem toEuclideanLin_kronecker_vecKron {m n m' n' : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m' m ℂ) (B : Matrix n' n ℂ)
    (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    toEuclideanLin (A ⊗ₖ B) (EuclideanSpace.vecKron x y) =
      EuclideanSpace.vecKron (toEuclideanLin A x) (toEuclideanLin B y) := by
  ext ⟨i, j⟩
  simp only [toLpLin_apply, PiLp.toLp_apply, EuclideanSpace.vecKron, mulVec, dotProduct,
    kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-- The permutation matrix of a bijection `e` sends the basis vector `|i⟩` to `|e i⟩`. -/
theorem toEuclideanLin_toPEquiv_toMatrix_single {α β : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] (e : α ≃ β) (i : α) :
    toEuclideanLin (e.symm.toPEquiv.toMatrix : Matrix β α ℂ) (EuclideanSpace.single i (1 : ℂ)) =
      EuclideanSpace.single (e i) (1 : ℂ) := by
  ext j
  simp only [toLpLin_apply, PiLp.toLp_apply, PiLp.ofLp_single, mulVec_single_one, col_apply,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    PiLp.single_apply, Equiv.symm_apply_eq]

end Matrix

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι]

/-- A coordinate vector `v` with `star v ⬝ᵥ v = 1` is a unit vector. -/
theorem norm_toLp_eq_one_of_star_dotProduct {v : ι → ℂ} (hv : star v ⬝ᵥ v = 1) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  have h2 : ((‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ : ℝ) : ℂ) ^ 2 = ((1 : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_one, one_pow]
    exact h.symm.trans hv
  have h3 : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 = (1 : ℝ) ^ 2 := by exact_mod_cast h2
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h3

/-- The coordinates `v` of a unit vector satisfy `star v ⬝ᵥ v = 1`. -/
theorem star_dotProduct_self_eq_one_of_norm_eq_one {v : EuclideanSpace ℂ ι} (hv : ‖v‖ = 1) :
    star v.ofLp ⬝ᵥ v.ofLp = 1 := by
  have h : (inner ℂ v v : ℂ) = ((‖v‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K v
  rw [EuclideanSpace.inner_eq_star_dotProduct, hv] at h
  rw [dotProduct_comm]
  simpa using h

end EuclideanSpace
