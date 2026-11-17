/-
Copyright (c) 2026 TNLean and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors, QICLean contributors
-/
import QICLean.Algebra.L2OpNormReindex
import QICLean.Algebra.MatrixKroneckerEmbed
import QICLean.Analysis.RootChannel
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norm after tensoring with an identity

Tensoring a square complex matrix with the identity of a nonempty finite space
preserves its Euclidean operator norm. The matrix space itself may have dimension zero.

The conclusion strengthens the reverse inequality proved in
`TNLean/MPS/AreaLaw/ViableSet/Gluing.lean`, commit
`111c9fe461af184e1aa20be8091ec1d1a775a68a`. The proof uses the existing
Kronecker star-algebra homomorphism and Mathlib's isometry theorem for injective
complex C-star-algebra homomorphisms, instead of extracting an isometric corner.

For rectangular matrices, tensoring with an identity on either side does not increase the
operator norm, and the operator norm is submultiplicative for Kronecker products, with no
nonemptiness hypothesis. `Matrix.l2_opNorm_one_kronecker_le` and
`Matrix.l2_opNorm_kronecker_le` are taken from TNLean,
`TNLean/Algebra/MatrixKroneckerContraction.lean` at commit `868d2c9`, where they are
`l2_opNorm_one_kronecker_rect_le` and `l2_opNorm_kronecker_le`. Changes: the first is renamed
and replaces QICLean's square `l2_opNorm_one_kronecker_le` (from
`QICLean/Analysis/TraceMulBound.lean`); the second replaces QICLean's square statement with
`Nonempty` hypotheses.

## Main results

* `Matrix.l2_opNorm_one_kronecker`, `Matrix.l2_opNorm_kronecker_one` — equality for a square
  matrix and a nonempty identity.
* `Matrix.l2_opNorm_one_kronecker_le` — `‖1 ⊗ B‖ ≤ ‖B‖`.
* `Matrix.l2_opNorm_kronecker_le` — `‖A ⊗ B‖ ≤ ‖A‖ ‖B‖`.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

/-- Tensoring a complex matrix with an identity on a nonempty finite space preserves
its Euclidean operator norm, including when the matrix has no rows or columns. -/
theorem l2_opNorm_one_kronecker {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] (K : Matrix Y Y ℂ) :
    ‖(1 : Matrix X X ℂ) ⊗ₖ K‖ = ‖K‖ := by
  change ‖rightKroneckerEmbed (m := X) K‖ = ‖K‖
  apply NonUnitalStarAlgHom.norm_map
  intro A B h
  ext i j
  simpa using congrFun (congrFun h (Classical.choice ‹Nonempty X›, i))
    (Classical.choice ‹Nonempty X›, j)

/-- Transposition preserves the Hilbert-space operator norm of a square complex matrix. -/
theorem l2_opNorm_transpose {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℂ) : ‖Aᵀ‖ = ‖A‖ := by
  let f : Matrix X X ℂ →⋆ₐ[ℂ] (Matrix X X ℂ)ᵐᵒᵖ :=
    { (transposeAlgEquiv X ℂ ℂ).toAlgHom with
      map_star' := fun A ↦ by
        apply MulOpposite.unop_injective
        rfl }
  exact NonUnitalStarAlgHom.norm_map f (transposeAlgEquiv X ℂ ℂ).injective A

/-- Tensoring with an identity on the right preserves the operator norm. -/
theorem l2_opNorm_kronecker_one {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty Y] (K : Matrix X X ℂ) :
    ‖K ⊗ₖ (1 : Matrix Y Y ℂ)‖ = ‖K‖ := by
  change ‖leftKroneckerEmbed (n := Y) K‖ = ‖K‖
  apply NonUnitalStarAlgHom.norm_map
  intro A B h
  ext i j
  simpa using congrFun (congrFun h (i, Classical.choice ‹Nonempty Y›))
    (j, Classical.choice ‹Nonempty Y›)

/-- Tensoring a rectangular matrix with an identity on the left does not increase its
operator norm. -/
theorem l2_opNorm_one_kronecker_le {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    [DecidableEq n] [DecidableEq κ] (B : Matrix m n ℂ) :
    ‖(1 : Matrix κ κ ℂ) ⊗ₖ B‖ ≤ ‖B‖ := by
  have h : (1 : Matrix κ κ ℂ) ⊗ₖ B =
      reindex (Equiv.prodComm m κ) (Equiv.prodComm n κ) (B ⊗ₖ (1 : Matrix κ κ ℂ)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [kroneckerMap_apply, mul_comm]
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_one_le B)

/-- Submultiplicativity of the operator norm for a tensor product of rectangular matrices. -/
theorem l2_opNorm_kronecker_le {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m']
    [Fintype n'] [DecidableEq m] [DecidableEq n] (A : Matrix m' m ℂ) (B : Matrix n' n ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  classical
  have h : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n' n' ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h]
  exact (l2_opNorm_mul _ _).trans (mul_le_mul (l2_opNorm_kronecker_one_le A)
    (l2_opNorm_one_kronecker_le B) (norm_nonneg _) (norm_nonneg _))

end Matrix
