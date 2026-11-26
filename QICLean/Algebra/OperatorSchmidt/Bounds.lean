/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import QICLean.Algebra.OperatorSchmidt.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Algebraic bounds for operator Schmidt rank

Concatenating and multiplying finite Kronecker decompositions gives addition
and multiplication bounds for operator Schmidt rank. Absorbing a scalar into
one local factor gives the scalar bound; subadditivity then gives the bound for
an arbitrary finite sum, including the empty sum. Empty local index types and
zero-rank matrices are included throughout.

These are the decomposition-length inequalities used in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 598–662, and ALVV,
arXiv:1602.08828v2, Proposition prop:Cheby-AGSP-eff, lines 1324–1332.
No locality or spectral assumptions enter these algebraic inequalities.

Moved from TNLean, `TNLean/MPS/MPU/Circuit/Gates/SchmidtSpanCuts.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open scoped BigOperators Kronecker

namespace Matrix

/-- Product-decomposition multiplication used in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–657, and ALVV,
arXiv:1602.08828v2, Proposition prop:Cheby-AGSP-eff, lines 1324–1332. -/
theorem operatorSchmidtRank_mul_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix (m × n) (m × n) ℂ) :
    operatorSchmidtRank (A * B) ≤
      operatorSchmidtRank A * operatorSchmidtRank B := by
  obtain ⟨U, V, hA⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank A
  obtain ⟨P, Q, hB⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank B
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨fun t => U (finProdFinEquiv.symm t).1 * P (finProdFinEquiv.symm t).2,
    fun t => V (finProdFinEquiv.symm t).1 * Q (finProdFinEquiv.symm t).2, ?_⟩
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun t : Fin (operatorSchmidtRank A) × Fin (operatorSchmidtRank B) =>
      (U t.1 * P t.2) ⊗ₖ (V t.1 * Q t.2)), Fintype.sum_prod_type]
  conv_lhs => rw [hA, hB]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_kronecker_mul]
  rw [Finset.sum_comm]

/-- Addition of product decompositions, as used in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 598–604 and 619–662. -/
theorem operatorSchmidtRank_add_le
    {m n : Type*} [Fintype m] [Finite n]
    (A B : Matrix (m × n) (m × n) ℂ) :
    operatorSchmidtRank (A + B) ≤
      operatorSchmidtRank A + operatorSchmidtRank B := by
  obtain ⟨U, V, hA⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank A
  obtain ⟨P, Q, hB⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank B
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨fun t => Sum.elim U P (finSumFinEquiv.symm t),
    fun t => Sum.elim V Q (finSumFinEquiv.symm t), ?_⟩
  rw [Equiv.sum_comp finSumFinEquiv.symm
    (fun t : Fin (operatorSchmidtRank A) ⊕ Fin (operatorSchmidtRank B) =>
      Sum.elim U P t ⊗ₖ Sum.elim V Q t), Fintype.sum_sum_type]
  exact congrArg₂ (· + ·) hA hB

/-- Scalar multiplication of a product decomposition, as used in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 633–644. -/
theorem operatorSchmidtRank_smul_le
    {m n : Type*} [Fintype m] [Finite n]
    (c : ℂ) (A : Matrix (m × n) (m × n) ℂ) :
    operatorSchmidtRank (c • A) ≤ operatorSchmidtRank A := by
  obtain ⟨U, V, hA⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank A
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨fun t => c • U t, V, ?_⟩
  conv_lhs => rw [hA]
  simp only [Finset.smul_sum, Matrix.smul_kronecker]

/-- Finite-sum product-decomposition bound used in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 598–604, 619–625, and 643–662. -/
theorem operatorSchmidtRank_sum_le
    {m n ι : Type*} [Fintype m] [Finite n]
    (s : Finset ι) (A : ι → Matrix (m × n) (m × n) ℂ) :
    operatorSchmidtRank (∑ i ∈ s, A i) ≤
      ∑ i ∈ s, operatorSchmidtRank (A i) := by
  refine Finset.le_sum_of_subadditive operatorSchmidtRank ?_
    operatorSchmidtRank_add_le s A
  exact operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨Fin.elim0, Fin.elim0, by simp⟩

end Matrix

section OperatorSchmidtProducts

/-!
# Elementary product bounds for operator Schmidt rank

An elementary Kronecker product has operator Schmidt rank at most one,
as does the identity. Empty local index types are included. These are the
product-rank base cases in AKLV, arXiv:1301.1162v1, Lemma 4.2, lines
626--657, and the physical parity-product bound in ALVV,
arXiv:1602.08828v2, `thm:FF-tH`, lines 1543--1568.
-/

open scoped Kronecker

namespace Matrix

/-- An elementary Kronecker product has operator Schmidt rank at most one.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--657. -/
theorem operatorSchmidtRank_kronecker_le_one {a b : Type*} [Fintype a] [Finite b]
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) : operatorSchmidtRank (A ⊗ₖ B) ≤ 1 := by
  exact operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨fun _ : Fin 1 ↦ A, fun _ : Fin 1 ↦ B, by simp⟩

/-- The identity has operator Schmidt rank at most one, including empty
local factors. This is the empty-product case of the parity-rank bound
in ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543--1568. -/
theorem operatorSchmidtRank_one_le {a b : Type*} [Fintype a] [DecidableEq a]
    [Finite b] [DecidableEq b] :
    operatorSchmidtRank (1 : Matrix (a × b) (a × b) ℂ) ≤ 1 := by
  simpa only [one_kronecker_one] using
    operatorSchmidtRank_kronecker_le_one (1 : Matrix a a ℂ) (1 : Matrix b b ℂ)

end Matrix

end OperatorSchmidtProducts

section

open scoped BigOperators

namespace Matrix

variable {K m n k : Type*} [Field K] [Fintype n] [Fintype k]

/-- Contracting the last coordinate by a scalar functional does not increase rank. -/
theorem rank_contract_right_le (M : Matrix m (n × k) K) (f : k → K) :
    Matrix.rank (fun i j => ∑ a : k, M i (j, a) * f a : Matrix m n K) ≤ M.rank := by
  classical
  let Q : Matrix (n × k) n K := fun r j => if r.1 = j then f r.2 else 0
  have hMQ : M * Q = fun i j => ∑ a : k, M i (j, a) * f a := by
    ext i j
    change (∑ r : n × k, M i r * Q r j) = _
    simp [Q, Fintype.sum_prod_type]
  rw [← hMQ]
  exact rank_mul_le_left M Q

/-- Contracting the first coordinate by a scalar functional does not increase rank. -/
theorem rank_contract_left_le [Finite m] (M : Matrix (k × m) n K) (f : k → K) :
    Matrix.rank (fun i j => ∑ a : k, f a * M (a, i) j : Matrix m n K) ≤ M.rank := by
  classical
  let : Fintype m := Fintype.ofFinite m
  let P : Matrix m (k × m) K := fun i r => if r.2 = i then f r.1 else 0
  have hPM : P * M = fun i j => ∑ a : k, f a * M (a, i) j := by
    ext i j
    change (∑ r : k × m, P i r * M r j) = _
    simp [P, Fintype.sum_prod_type]
  rw [← hPM]
  exact rank_mul_le_right P M

end Matrix

end
