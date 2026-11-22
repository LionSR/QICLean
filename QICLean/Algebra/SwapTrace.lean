/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import QICLean.Channel.MaximallyEntangled
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The swap matrix against Kronecker products

This file proves the trace identity used to contract a swap operator against a
Kronecker product, the exchange of the two factors of a Kronecker product by the swap
matrix, and the unitarity of the swap matrix between its two product-coordinate orders.

## Main results

* `Matrix.trace_swapMatrix_mul_kronecker`: the swap contraction equals the trace of the
  product of the two factors.
* `Matrix.trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup`: the
  contraction of a unitary with its conjugate transpose equals its dimension.
* `Matrix.swapMatrix_mul_kronecker`, `Matrix.kronecker_mul_swapMatrix`: the swap matrix
  exchanges the two factors of a Kronecker product.
* `Matrix.trace_swapMatrix_mul_of_eq_smul_kronecker_conjTranspose`: contracting the swap
  matrix against a scalar multiple of `x ⊗ x†` for unitary `x` returns the scalar times the
  factor dimension.
* `Matrix.swapMatrix_isUnitaryBetween`: the swap matrix is unitary between its source and
  target product-coordinate orders.

The last three groups were moved from TNLean, `TNLean/Algebra/SwapKronecker.lean` and
`TNLean/Algebra/SwapMatrix.lean` at commit `49b78ed821` (Apache-2.0).

## References

* [J. I. Cirac et al., *Matrix product unitaries: structure, symmetries, and topological
  invariants*, arXiv:1703.09188, lines 1316--1319, 1608--1610, 1624--1630, and
  2009--2034][Cirac2017MPU]
-/

open scoped Matrix Kronecker BigOperators

namespace Matrix

variable {n : ℕ}

/-- Contracting the swap matrix with a Kronecker product gives the trace of the product,
with the factor order used in arXiv:1703.09188, lines 1608--1610. -/
theorem trace_swapMatrix_mul_kronecker
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (swapMatrix n * (A ⊗ₖ B)).trace = (A * B).trace := by
  classical
  have hinner (i j k : Fin n) :
      (∑ l : Fin n, (if i = l ∧ j = k then 1 else 0) * (A k i * B l j)) =
        if j = k then A k i * B i j else 0 := by
    by_cases hjk : j = k
    · subst k
      simp
    · simp [hjk]
  have hmiddle (i j : Fin n) :
      (∑ k : Fin n, if j = k then A k i * B i j else 0) = A j i * B i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (if i = l ∧ j = k then 1 else 0) * (A k i * B l j)) =
      ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if j = k then A k i * B i j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact hinner i j k
      _ = ∑ i : Fin n, ∑ j : Fin n, A j i * B i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hmiddle i j
      _ = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
        rw [Finset.sum_comm]
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    swapMatrix_apply, Matrix.kroneckerMap_apply] using hsum

/-- For a unitary matrix, contracting the swap matrix with the Kronecker product of the
matrix and its conjugate transpose gives the matrix dimension. -/
theorem trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ unitaryGroup (Fin n) ℂ) :
    (swapMatrix n * (A ⊗ₖ Aᴴ)).trace = (n : ℂ) := by
  rw [trace_swapMatrix_mul_kronecker]
  have hunit : A * Aᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hA
  rw [hunit, Matrix.trace_one, Fintype.card_fin]

/-- The swap matrix intertwines the two orders of a Kronecker
product: `𝕊(A ⊗ B) = (B ⊗ A)𝕊`.

This is one side of the exchange identity in arXiv:1703.09188,
`paper_v2.tex` lines 1316--1319, and is the algebraic step behind the gauge
invariance asserted at lines 1624--1630. -/
theorem swapMatrix_mul_kronecker (A B : Matrix (Fin n) (Fin n) ℂ) :
    swapMatrix n * (A ⊗ₖ B) = (B ⊗ₖ A) * swapMatrix n := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    ite_and, Finset.sum_ite_eq, mul_comm]

/-- The swap matrix read from the other side:
`(A ⊗ B)𝕊 = 𝕊(B ⊗ A)`. -/
theorem kronecker_mul_swapMatrix (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A ⊗ₖ B) * swapMatrix n = swapMatrix n * (B ⊗ₖ A) :=
  (swapMatrix_mul_kronecker B A).symm

/-- Contracting the swap matrix against a scalar multiple of
`x ⊗ x†`, for a unitary `x`, returns the scalar times the factor dimension.

The general identity gives `tr[𝕊(x ⊗ x†)] = n`; for `x` acting on a space of dimension `d²`
this is the value `d²` in arXiv:1703.09188, `paper_v2.tex` lines 1608--1610. -/
theorem trace_swapMatrix_mul_of_eq_smul_kronecker_conjTranspose
    {M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} {x : Matrix (Fin n) (Fin n) ℂ}
    (σ : ℂ) (hx : x ∈ unitaryGroup (Fin n) ℂ) (hM : M = σ • (x ⊗ₖ xᴴ)) :
    (swapMatrix n * M).trace = σ * n := by
  rw [hM, Matrix.mul_smul, Matrix.trace_smul,
    trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup x hx, smul_eq_mul]

/-- The swap matrix is unitary between its product-coordinate spaces.

With columns as source coordinates and rows as target coordinates, `swapMatrix d` sends the
source coordinate `(i, j)` to the target coordinate `(j, i)`. This is the exchange matrix
of arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3`
(lines 2009--2034), and the endpoint of the unitary interpolation at lines 2148--2150. -/
theorem swapMatrix_isUnitaryBetween (d : ℕ) :
    (swapMatrix d).IsUnitaryBetween := by
  rw [IsUnitaryBetween, IsIsometry, IsCoisometry, swapMatrix_conjTranspose]
  exact ⟨swapMatrix_mul_self, swapMatrix_mul_self⟩

end Matrix
