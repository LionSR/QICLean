/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MonomialEvaluationSchmidtRank

/-! # Axiom check and empty and dependent coefficient applications -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- info:
'Matrix.operatorSchmidtRank_sum_le_of_monomial_evaluations'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_sum_le_of_monomial_evaluations

namespace Matrix

private theorem zero_rank_bound {l n : Type*} [Fintype l] [Finite n] :
    operatorSchmidtRank (0 : Matrix (l × n) (l × n) ℂ) ≤ 0 :=
  operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨Fin.elim0, Fin.elim0, by simp⟩

-- Empty monomial support entails an empty selected sum, even for an arbitrary coefficient family.
example {σ l n : Type*} [Fintype l] [Finite n]
    (f : (σ →₀ ℕ) → Matrix (l × n) (l × n) ℂ) :
    operatorSchmidtRank (∑ α ∈ (∅ : Finset (σ →₀ ℕ)), f α) ≤ 0 := by
  simpa using operatorSchmidtRank_sum_le_of_monomial_evaluations (∅ : Finset (σ →₀ ℕ))
    f ∅ (Finset.Subset.refl _) 0 (fun _ ↦ by simpa using zero_rank_bound (l := l) (n := n))

-- The selected subset may be empty independently of the prescribed support.
example {σ l n : Type*} [Fintype l] [Finite n]
    (S : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → Matrix (l × n) (l × n) ℂ) (r : ℕ)
    (h : ∀ z : σ → ℂ, operatorSchmidtRank
      (∑ α ∈ S, MvPolynomial.eval z (MvPolynomial.monomial α (1 : ℂ)) • f α) ≤ r) :
    operatorSchmidtRank (∑ α ∈ (∅ : Finset (σ →₀ ℕ)), f α) ≤ S.card * r :=
  operatorSchmidtRank_sum_le_of_monomial_evaluations S f ∅ (Finset.empty_subset _) r h

private abbrev OneFactor := Matrix (Unit × Unit) (Unit × Unit) ℂ

private theorem one_dimensional_rank_bound (X : OneFactor) : operatorSchmidtRank X ≤ 1 := by
  simpa [Matrix.operatorSchmidtRank, Module.finrank_matrix] using
    LinearMap.finrank_range_le (Matrix.operatorSchmidtMap X)

-- Two distinct monomials have the same nonzero identity coefficient.
-- Their evaluated matrices need not be independent; every evaluation still has rank at most one.
example : operatorSchmidtRank (1 : OneFactor) ≤ 2 := by
  have h := operatorSchmidtRank_sum_le_of_monomial_evaluations
    ({0, Finsupp.single () 1} : Finset (Unit →₀ ℕ))
    (fun _ ↦ (1 : OneFactor)) {0} (by simp) 1
    (fun _ ↦ one_dimensional_rank_bound _)
  exact (show operatorSchmidtRank (1 : OneFactor) ≤
      ({0, Finsupp.single () 1} : Finset (Unit →₀ ℕ)).card by simpa using h).trans
    Finset.card_le_two

end Matrix
