/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtBounds
import QICLean.Entropy.FilterChainEnergy
import QICLean.Entropy.SupportedOperatorSchmidtRank

/-!
# Operator Schmidt rank of ordered local products

Across a cut, each crossing occurrence contributes the square of the dimension
on its inside support. One-sided occurrences do not increase the rank bound.
The exponent counts occurrences, so repeated letters retain their multiplicities.
No commutation, positivity, state or spectral hypothesis is needed.

This is the word-decomposition step in LVV, arXiv:1307.5143v1, equation
e:decomp, lines 584–588, and AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 646–653. Polynomial collection and the final polynomial rank estimates
are separate results.

**Local fix (paired indices):** The two local factors in the matrix-unit
expansion are indexed by the same pair. The independently indexed expression
printed at LVV line 584 would have rank at most one; the correction and a
positive-contraction example are recorded in
`docs/paper-gaps/lvv13_paired_matrix_decomposition.tex`.
-/

open scoped BigOperators Kronecker

namespace Entropy

open Classical in
/-- Weighted support bound for an ordered product. LVV,
arXiv:1307.5143v1, equation e:decomp, lines 584–588; AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–653. -/
theorem operatorSchmidtRank_cutOperator_list_prod_le
    {V κ : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : Finset V) (X : κ → Finset V)
    (P : κ → Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : ∀ t, IsSupportedOn (n := fun _ : V => q) (P t) (X t))
    (w : List κ) :
    Matrix.operatorSchmidtRank
      (cutOperator (n := fun _ : V => q) A ((w.map P).prod)) ≤
      q ^ (2 * (((w.filter (fun t => ¬ (X t ⊆ A ∨ Disjoint (X t) A))).map
        (fun t => (X t ∩ A).card)).sum)) := by
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.filter_nil, List.sum_nil,
      Nat.mul_zero, pow_zero]
    have h1 := isSupportedOn_one (n := fun _ : V => q) (∅ : Finset V)
    exact h1.operatorSchmidtRank_cutOperator_le_one (A := A) (Or.inl (Finset.empty_subset A))
  | cons t w ih =>
    simp only [List.map_cons, List.prod_cons, cutOperator_mul]
    by_cases hside : X t ⊆ A ∨ Disjoint (X t) A
    case neg =>
      simp only [List.filter_cons, decide_eq_true_eq, hside, not_false_eq_true,
        ↓reduceIte, List.map_cons, List.sum_cons]
      have hhead : Matrix.operatorSchmidtRank (cutOperator A (P t)) ≤
          q ^ (2 * (X t ∩ A).card) := by
        simpa only [Finset.prod_const, ← pow_mul, Nat.mul_comm] using
          (hP t).operatorSchmidtRank_cutOperator_le (A := A)
      simpa only [← pow_add, Nat.mul_add] using
        (Matrix.operatorSchmidtRank_mul_le _ _).trans (Nat.mul_le_mul hhead ih)
    simp only [List.filter_cons, decide_eq_true_eq, hside, not_true_eq_false,
      ↓reduceIte]
    simpa only [one_mul] using
      (Matrix.operatorSchmidtRank_mul_le _ _).trans
        (Nat.mul_le_mul ((hP t).operatorSchmidtRank_cutOperator_le_one hside) ih)

end Entropy
