/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt

/-!
# Restricting the local coordinates of a bipartite operator

Fixing separate product-basis coordinates on the exterior sites does not
increase the operator Schmidt rank at an internal cut. This is the elementary restriction
of product factors used in ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1311–1333.
-/

open scoped BigOperators Kronecker

namespace Matrix

/-- Independent row and column restrictions on the two tensor factors do not
increase operator Schmidt rank. ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1316–1333. No injectivity or nonempty-index hypothesis is needed. -/
theorem operatorSchmidtRank_submatrix_prod_le
    {m n m' n' : Type*} [Fintype m] [Finite n] [Fintype m'] [Finite n']
    (M : Matrix (m × n) (m × n) ℂ)
    (rL cL : m' → m) (rR cR : n' → n) :
    operatorSchmidtRank (M.submatrix (Prod.map rL rR) (Prod.map cL cR)) ≤
      operatorSchmidtRank M := by
  classical
  obtain ⟨A, B, hM⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank M
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨fun t ↦ (A t).submatrix rL cL, fun t ↦ (B t).submatrix rR cR, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [hM, Matrix.sum_apply, Matrix.submatrix_apply]

/-- Fixing exterior row and column coordinates preserves the internal rank
bound. This partial matrix element is an auxiliary for the factor MPOs in
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333. -/
theorem operatorSchmidtRank_fix_outer_le
    {a b c d : Type*} [Fintype a] [Fintype b] [Finite c] [Finite d]
    (M : Matrix ((a × b) × (c × d)) ((a × b) × (c × d)) ℂ)
    (a₁ a₂ : a) (d₁ d₂ : d) :
    operatorSchmidtRank (M.submatrix
      (fun x : b × c ↦ ((a₁, x.1), (x.2, d₁)))
      (fun y : b × c ↦ ((a₂, y.1), (y.2, d₂)))) ≤ operatorSchmidtRank M := by
  exact operatorSchmidtRank_submatrix_prod_le M
    (fun x ↦ (a₁, x)) (fun x ↦ (a₂, x)) (fun y ↦ (y, d₁)) (fun y ↦ (y, d₂))

end Matrix
