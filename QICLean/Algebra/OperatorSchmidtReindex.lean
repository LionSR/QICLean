/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt

/-!
# Operator Schmidt rank under separate coordinate changes

Separate changes of coordinates on the two finite tensor factors preserve
operator Schmidt rank. Transporting a shortest product decomposition gives
one inequality; the inverse coordinate changes give the other. Empty finite
factors and zero rank are included.

The product decomposition is that of arXiv:1903.05373, equation (1).
The same coordinate invariance is used when moving the cuts in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
-/

namespace Matrix

/-- Separate local coordinate changes preserve the length of a product
decomposition, arXiv:1903.05373, equation (1). -/
private theorem operatorSchmidtRank_reindex_prodCongr_le
    {m n m' n' : Type*} [Fintype m] [Fintype m'] [Finite n] [Finite n']
    (ρ : Matrix (m × n) (m × n) ℂ) (eL : m ≃ m') (eR : n ≃ n') :
    operatorSchmidtRank (ρ.reindex (eL.prodCongr eR) (eL.prodCongr eR)) ≤
      operatorSchmidtRank ρ := by
  obtain ⟨A, B, hρ⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank ρ
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨fun t ↦ (A t).reindex eL eL, fun t ↦ (B t).reindex eR eR, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [hρ, reindex_apply, Matrix.sum_apply]

/-- Separate changes of coordinates on the two tensor factors preserve
operator Schmidt rank. This is the invariance of the product decomposition
in arXiv:1903.05373, equation (1), used in the movement of cuts in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
Empty finite tensor factors are included. -/
theorem operatorSchmidtRank_reindex_prodCongr
    {m n m' n' : Type*} [Fintype m] [Fintype m'] [Finite n] [Finite n']
    (ρ : Matrix (m × n) (m × n) ℂ) (eL : m ≃ m') (eR : n ≃ n') :
    Matrix.operatorSchmidtRank
        (ρ.reindex (eL.prodCongr eR) (eL.prodCongr eR)) =
      Matrix.operatorSchmidtRank ρ := by
  refine Nat.le_antisymm (operatorSchmidtRank_reindex_prodCongr_le ρ eL eR) ?_
  simpa only [← Equiv.prodCongr_symm, ← reindex_symm, Equiv.symm_apply_apply] using
    operatorSchmidtRank_reindex_prodCongr_le
      (ρ.reindex (eL.prodCongr eR) (eL.prodCongr eR)) eL.symm eR.symm

end Matrix
