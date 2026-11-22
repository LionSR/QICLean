/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Permutation matrices: invariant matrices and products

Simultaneous permutation invariance of the entries of a matrix is equivalent to commuting with
the corresponding permutation matrix; this is the finite coordinate symmetry step of Schuch,
Cirac, and Pérez-García, arXiv:1001.3807, lines 2505–2558. The matrix of a product permutation
is the Kronecker product of the factor matrices.

Moved from TNLean, `TNLean/Algebra/PermutationMatrixCommutation.lean` and
`Matrix.permMatrixHom_prodCongr` of `TNLean/Algebra/RegularRepresentationBlocking.lean`, at
commit `49b78ed821` (Apache-2.0).

## Main results

* `Matrix.commute_permMatrix_of_entry_invariant`
* `Matrix.permMatrixHom_prodCongr`
-/

open scoped Kronecker

namespace Matrix
variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]

/-- A matrix with permutation-invariant entries commutes with the actual permutation
matrix. This is the finite-coordinate symmetry step in SCP10, lines 2505–2558. -/
theorem commute_permMatrix_of_entry_invariant (A : Matrix ι ι R) (τ : Equiv.Perm ι)
    (h : ∀ a b, A (τ a) (τ b) = A a b) : Commute A (τ.permMatrix R) := by
  change A * τ.permMatrix R = τ.permMatrix R * A
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext a b
  exact (h a (τ.symm b)).symm.trans (by simp)

/-- The matrix of a product permutation is the Kronecker product of its factor matrices. -/
theorem permMatrixHom_prodCongr {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    permMatrixHom (R := ℂ) (Equiv.prodCongr σ τ) =
      permMatrixHom (R := ℂ) σ ⊗ₖ permMatrixHom (R := ℂ) τ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [permMatrixHom_apply, Equiv.Perm.permMatrix,
    Prod.ext_iff, Equiv.Perm.inv_def]
  split_ifs <;> simp_all

end Matrix
