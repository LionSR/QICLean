/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Linear maps on matrices of a product are determined on Kronecker products

The matrices of `α × α'` are the tensor product of the matrices of `α` and of `α'`, so the
Kronecker products `x ⊗ₖ y` span them, and two linear maps that agree on them are equal.

## Main results

* `Matrix.linearMap_ext_kronecker` — linear maps agreeing on Kronecker products are equal.
-/

open scoped Kronecker

namespace Matrix

/-- Two linear maps on the matrices of `α × α'` that agree on all Kronecker products are equal:
the Kronecker products span. -/
theorem linearMap_ext_kronecker {α α' M : Type*} [Finite α] [Finite α'] [AddCommMonoid M]
    [Module ℂ M] {f g : Matrix (α × α') (α × α') ℂ →ₗ[ℂ] M}
    (h : ∀ x y, f (x ⊗ₖ y) = g (x ⊗ₖ y)) : f = g := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite α'
  have : f ∘ₗ (kroneckerLinearEquiv α α α' α' ℂ).toLinearMap =
      g ∘ₗ (kroneckerLinearEquiv α α α' α' ℂ).toLinearMap :=
    TensorProduct.ext' fun x y ↦ h x y
  ext X
  simpa using LinearMap.congr_fun this ((kroneckerLinearEquiv α α α' α' ℂ).symm X)

end Matrix
