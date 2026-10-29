/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtCut

/-!
# Operator Schmidt rank under changes of bipartition

Separate changes of coordinates on the two finite tensor factors preserve
operator Schmidt rank. Transporting a shortest product decomposition gives
one inequality; the inverse coordinate changes give the other. Empty finite
factors and zero rank are included.

Interchanging two finite factors on opposite sides of a cut increases the
rank by at most the product of their squared dimensions. The two unchanged
factors do not contribute to this bound.

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

/-- Exchanging the two inner finite tensor factors across an operator Schmidt
cut costs at most their squared dimensions. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
Empty finite factors are included. -/
theorem operatorSchmidtRank_reindex_prodProdProdComm_le
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Finite d]
    (ρ : Matrix ((a × b) × (c × d)) ((a × b) × (c × d)) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodProdProdComm a b c d)
          (Equiv.prodProdProdComm a b c d)) ≤
      Fintype.card b ^ 2 * Fintype.card c ^ 2 * operatorSchmidtRank ρ := by
  let e : b × (c × d) ≃ c × (b × d) :=
    (Equiv.prodAssoc b c d).symm.trans
      (((Equiv.prodComm b c).prodCongr (Equiv.refl d)).trans
        (Equiv.prodAssoc c b d))
  let σ := ρ.reindex (Equiv.prodAssoc a b (c × d)) (Equiv.prodAssoc a b (c × d))
  let τ := σ.reindex ((Equiv.refl a).prodCongr e) ((Equiv.refl a).prodCongr e)
  have hreindex : τ.reindex (Equiv.prodAssoc a c (b × d)).symm
      (Equiv.prodAssoc a c (b × d)).symm =
      ρ.reindex (Equiv.prodProdProdComm a b c d)
        (Equiv.prodProdProdComm a b c d) := by rfl
  refine (hreindex ▸ operatorSchmidtRank_reindex_prodAssoc_symm_le τ).trans ?_
  rw [show operatorSchmidtRank τ = operatorSchmidtRank σ from
    operatorSchmidtRank_reindex_prodCongr σ (Equiv.refl a) e]
  exact (Nat.mul_le_mul_left (Fintype.card c ^ 2)
    (operatorSchmidtRank_reindex_prodAssoc_le ρ)).trans_eq (by ac_rfl)

end Matrix
