/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring

/-! # Kronecker products of complex vectors -/

open scoped Kronecker

/-- Kronecker product of two vectors: `(vecKronecker a b) (i, j) = a i * b j`. -/
def Matrix.vecKronecker {α β : Type*} (a : α → ℂ) (b : β → ℂ) : α × β → ℂ :=
  fun p => a p.1 * b p.2

@[simp]
theorem Matrix.vecKronecker_apply {α β : Type*} (a : α → ℂ) (b : β → ℂ) (i : α) (j : β) :
    Matrix.vecKronecker a b (i, j) = a i * b j := rfl

/-- The outer product of two Kronecker vectors is the Kronecker product of their outer products. -/
theorem Matrix.vecMulVec_vecKronecker {α β : Type*}
    (a₁ a₂ : α → ℂ) (b₁ b₂ : β → ℂ) :
    Matrix.vecMulVec (Matrix.vecKronecker a₁ b₁) (star (Matrix.vecKronecker a₂ b₂)) =
      Matrix.vecMulVec a₁ (star a₂) ⊗ₖ Matrix.vecMulVec b₁ (star b₂) := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  simp only [Matrix.vecMulVec_apply, Matrix.vecKronecker_apply, Pi.star_apply,
    star_mul', Matrix.kroneckerMap_apply]
  ring
