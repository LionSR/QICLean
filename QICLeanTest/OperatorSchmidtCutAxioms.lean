/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtCut

/-! # Axiom checks and unit- and empty-factor cut applications -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.operatorSchmidtRank_le_card_of_blocks_mem_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_le_card_of_blocks_mem_span

/-- info:
'Matrix.operatorSchmidtRank_reindex_prodAssoc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_reindex_prodAssoc_le

/-- info:
'Matrix.operatorSchmidtRank_reindex_prodAssoc_symm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_reindex_prodAssoc_symm_le

/-- info:
'Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition

open Matrix

example {l n : Type*} [Fintype l] [Fintype n]
    (ρ : Matrix (l × (PUnit × n)) (l × (PUnit × n)) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l PUnit n).symm (Equiv.prodAssoc l PUnit n).symm) ≤
      operatorSchmidtRank ρ := by
  simpa using operatorSchmidtRank_reindex_prodAssoc_symm_le ρ

example {l n : Type*} [Fintype l] [Fintype n]
    (ρ : Matrix (l × (Empty × n)) (l × (Empty × n)) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l Empty n).symm (Equiv.prodAssoc l Empty n).symm) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using operatorSchmidtRank_reindex_prodAssoc_symm_le ρ)

example {l n : Type*} [Fintype l] [Fintype n]
    (ρ : Matrix ((l × PUnit) × n) ((l × PUnit) × n) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l PUnit n) (Equiv.prodAssoc l PUnit n)) ≤
      operatorSchmidtRank ρ := by
  simpa using operatorSchmidtRank_reindex_prodAssoc_le ρ

example {l n : Type*} [Fintype l] [Fintype n]
    (ρ : Matrix ((l × Empty) × n) ((l × Empty) × n) ℂ) :
    operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l Empty n) (Equiv.prodAssoc l Empty n)) = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using operatorSchmidtRank_reindex_prodAssoc_le ρ)

