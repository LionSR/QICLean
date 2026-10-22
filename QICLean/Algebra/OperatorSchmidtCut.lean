/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt

/-!
# Operator Schmidt rank under movement of a cut

For three finite tensor factors, moving the middle factor across the cut
increases operator Schmidt rank by at most the square of its dimension.
Both directions are included, without a nonemptiness hypothesis.

A minimal product decomposition supplies a finite spanning family for the
new operator blocks. The family is indexed by a decomposition term and a pair
of middle-factor indices.

These are the linear-algebraic estimates used in AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 651–654. The identification of chain cuts with these
three factors is a separate geometric step.
-/

open scoped BigOperators Kronecker

namespace Matrix

/-- Moving a finite tensor factor across an operator Schmidt cut costs
at most its squared dimension. Supporting algebra for AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 651–654. -/
theorem operatorSchmidtRank_reindex_prodAssoc_symm_le
    {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix (l × (m × n)) (l × (m × n)) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l m n).symm (Equiv.prodAssoc l m n).symm) ≤
      Fintype.card m ^ 2 * operatorSchmidtRank ρ := by
  classical
  let := Fintype.ofFinite n
  obtain ⟨A, B, hρ⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank ρ
  let σ := ρ.reindex (Equiv.prodAssoc l m n).symm (Equiv.prodAssoc l m n).symm
  have hblock (ij : (l × m) × (l × m)) :
      operatorBlock σ ij.1 ij.2 =
        ∑ t, A t ij.1.1 ij.2.1 • operatorBlock (B t) ij.1.2 ij.2.2 := by
    ext a b
    simp [σ, hρ, operatorBlock, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  let C : Fin (operatorSchmidtRank ρ) × (m × m) → Matrix n n ℂ :=
    fun t ↦ operatorBlock (B t.1) t.2.1 t.2.2
  change operatorSchmidtRank σ ≤ _
  calc
    operatorSchmidtRank σ ≤ Fintype.card (Fin (operatorSchmidtRank ρ) × (m × m)) := by
      apply operatorSchmidtRank_le_card_of_blocks_mem_span σ C
      intro i j
      rw [hblock (i, j)]
      exact Submodule.sum_smul_mem _ _ fun t _ ↦
        Submodule.subset_span ⟨(t, i.2, j.2), rfl⟩
    _ = Fintype.card m ^ 2 * operatorSchmidtRank ρ := by
      simp [pow_two, Nat.mul_comm, Nat.mul_assoc]

/-- The same cut-movement estimate with the middle tensor factor moved from left to right.
Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 651–654. -/
theorem operatorSchmidtRank_reindex_prodAssoc_le
    {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n)) ≤
      Fintype.card m ^ 2 * operatorSchmidtRank ρ := by
  classical
  let := Fintype.ofFinite n
  obtain ⟨A, B, hρ⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank ρ
  let σ := ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n)
  let C : Fin (operatorSchmidtRank ρ) × (m × m) → Matrix (m × n) (m × n) ℂ :=
    fun t ↦ single t.2.1 t.2.2 1 ⊗ₖ B t.1
  have hblock (ij : l × l) :
      operatorBlock σ ij.1 ij.2 =
        ∑ t, A t.1 (ij.1, t.2.1) (ij.2, t.2.2) • C t := by
    ext a b
    simp [σ, C, hρ, operatorBlock, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Matrix.single_apply, ite_and]
  change operatorSchmidtRank σ ≤ _
  calc
    operatorSchmidtRank σ ≤ Fintype.card (Fin (operatorSchmidtRank ρ) × (m × m)) := by
      apply operatorSchmidtRank_le_card_of_blocks_mem_span σ C
      intro i j
      rw [hblock (i, j)]
      exact Submodule.sum_smul_mem _ _ fun t _ ↦ Submodule.subset_span ⟨t, rfl⟩
    _ = Fintype.card m ^ 2 * operatorSchmidtRank ρ := by
      simp [pow_two, Nat.mul_comm, Nat.mul_assoc]

end Matrix
