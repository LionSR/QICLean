/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexed sandwich products

A product `M ρ Nᴴ` of complex matrices whose outer factors are reindexed along `e` in the rows and
`f` in the columns is the reindexing along `e` of the product of the original factors around `ρ`
read back along `f`.

## Main results

* `Matrix.reindex_mul_mul_conjTranspose`.
-/

namespace Matrix

/-- **Reindexing a sandwich product**: `M' ρ N'ᴴ`, for `M'`, `N'` the reindexings of `M`, `N`
along `e` and `f`, is the reindexing along `e` of `M ρ' Nᴴ`, for `ρ'` the reindexing of `ρ`
along `f⁻¹`. -/
theorem reindex_mul_mul_conjTranspose {m m' n n' : Type*} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (M N : Matrix m n ℂ) (ρ : Matrix n' n' ℂ) :
    reindex e f M * ρ * (reindex e f N)ᴴ =
      reindex e e (M * reindex f.symm f.symm ρ * Nᴴ) := by
  ext i j
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, mul_apply, conjTranspose_apply]
  rw [← f.sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← f.sum_comp]
  simp

end Matrix
