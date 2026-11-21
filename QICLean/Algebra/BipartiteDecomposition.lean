/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QICLean.Algebra.OperatorSchmidt

/-!
# One-sided operators and product decompositions on a bipartite space

On `ℂ^α ⊗ ℂ^β`, an operator is one-sided when it is `A ⊗ 1` or `1 ⊗ A`, and it has a product
decomposition with constants `c₀` and `N` when it is a sum of at most `N` products `c ⊗ d`
with `‖c‖ ‖d‖ ≤ c₀`. These are the two shapes of a term crossing a cut in the marginal-tail
estimate of the area-law manuscript, `02-initial.tex`, lines 126–133.

A product decomposition is an operator-Schmidt decomposition with at most `N` summands whose
factors obey the norm bound, so it bounds the operator Schmidt rank by `N`.

## Main definitions

* `Matrix.IsOneSided`, `Matrix.HasProductDecomposition`.

## Main results

* `Matrix.HasProductDecomposition.exists_hasOperatorSchmidtDecomposition`,
  `Matrix.HasProductDecomposition.operatorSchmidtRank_le`.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- An operator acts on a single tensor factor: it is `A ⊗ 1` or `1 ⊗ A`. -/
def IsOneSided (X : Matrix (α × β) (α × β) ℂ) : Prop :=
  (∃ A : Matrix α α ℂ, X = A ⊗ₖ (1 : Matrix β β ℂ)) ∨
    ∃ A : Matrix β β ℂ, X = (1 : Matrix α α ℂ) ⊗ₖ A

/-- An operator is a sum of at most `N` products `c_a ⊗ d_a` with
`‖c_a‖ ‖d_a‖ ≤ c₀`. For a term supported on sites of total dimension `d` this holds
with `N = d²`, through matrix units on the portion of the support in the first factor.
Area-law manuscript, `02-initial.tex`, lines 126–133. -/
def HasProductDecomposition (X : Matrix (α × β) (α × β) ℂ) (c₀ : ℝ) (N : ℕ) : Prop :=
  ∃ (M : ℕ) (c : Fin M → Matrix α α ℂ) (d : Fin M → Matrix β β ℂ),
    M ≤ N ∧ X = ∑ a, c a ⊗ₖ d a ∧ ∀ a, ‖c a‖ * ‖d a‖ ≤ c₀

/-- Forgetting the norm bound, a product decomposition with constants `c₀` and `N` is an
operator-Schmidt decomposition with at most `N` summands. -/
theorem HasProductDecomposition.exists_hasOperatorSchmidtDecomposition
    {X : Matrix (α × β) (α × β) ℂ} {c₀ : ℝ} {N : ℕ} (h : X.HasProductDecomposition c₀ N) :
    ∃ M ≤ N, X.HasOperatorSchmidtDecomposition M := by
  obtain ⟨M, c, d, hM, hX, -⟩ := h
  exact ⟨M, hM, c, d, hX⟩

/-- An operator with a product decomposition with constants `c₀` and `N` has operator Schmidt
rank at most `N`. -/
theorem HasProductDecomposition.operatorSchmidtRank_le {X : Matrix (α × β) (α × β) ℂ} {c₀ : ℝ}
    {N : ℕ} (h : X.HasProductDecomposition c₀ N) : X.operatorSchmidtRank ≤ N := by
  obtain ⟨M, hM, hX⟩ := h.exists_hasOperatorSchmidtDecomposition
  exact (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition hX).trans hM

end Matrix
