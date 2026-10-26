/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fintype.BigOperators
import QICLean.Channel.FiniteProductOperatorSchmidt

/-! # Vacuum, empty local alphabet and unequal regions -/

open scoped symmDiff

-- Unequal exchanged-region sizes give 2^(2*3)=64.
example (M : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) :
    Matrix.operatorSchmidtRank
      (M.reindex (FiniteProduct.splitEquiv (fun _ : Fin 3 ↦ Fin 2) {2})
        (FiniteProduct.splitEquiv (fun _ : Fin 3 ↦ Fin 2) {2})) ≤
      64 * Matrix.operatorSchmidtRank
        (M.reindex (FiniteProduct.splitEquiv (fun _ : Fin 3 ↦ Fin 2) {0, 1})
          (FiniteProduct.splitEquiv (fun _ : Fin 3 ↦ Fin 2) {0, 1})) := by
  have hcard : (({0, 1} ∆ {2}) : Finset (Fin 3)).card = 3 := by decide
  have hpow : (2 : ℕ) ^ (2 * 3) = 64 := by decide
  simpa only [hcard, hpow] using FiniteProduct.operatorSchmidtRank_splitEquiv_le 2
    ({0, 1} : Finset (Fin 3)) {2} M

-- An empty local alphabet on a nonempty site set has zero changed-cut rank.
example (M : Matrix (Fin 1 → Fin 0) (Fin 1 → Fin 0) ℂ) :
    Matrix.operatorSchmidtRank
      (M.reindex (FiniteProduct.splitEquiv (fun _ : Fin 1 ↦ Fin 0) {0})
        (FiniteProduct.splitEquiv (fun _ : Fin 1 ↦ Fin 0) {0})) ≤ 0 := by
  have hcard : ((∅ ∆ {0}) : Finset (Fin 1)).card = 1 := by decide
  have hpow : (0 : ℕ) ^ (2 * 1) = 0 := by decide
  simpa only [hcard, hpow, Nat.zero_mul] using
    FiniteProduct.operatorSchmidtRank_splitEquiv_le 0 (∅ : Finset (Fin 1)) {0} M

-- The empty site set retains its vacuum configuration, even for q = 0.
example (S T : Finset (Fin 0)) (M : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ) :
    Matrix.operatorSchmidtRank
      (M.reindex (FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) T)
        (FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) T)) ≤
      Matrix.operatorSchmidtRank
        (M.reindex (FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) S)
          (FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) S)) := by
  have hcard : (S ∆ T).card = 0 := by
    rw [Finset.eq_empty_of_isEmpty (S ∆ T), Finset.card_empty]
  simpa only [hcard, Nat.mul_zero, pow_zero, one_mul] using
    FiniteProduct.operatorSchmidtRank_splitEquiv_le 0 S T M

-- The vacuum cut has a nonzero operator, so its rank is not forced to zero.
example : 0 < Matrix.operatorSchmidtRank
    ((1 : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ).reindex
      (FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) ∅)
      (FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) ∅)) := by
  apply Matrix.operatorSchmidtRank_pos_of_ne_zero
  intro h
  let x := FiniteProduct.splitEquiv (fun _ : Fin 0 ↦ Fin 0) ∅
    (fun v ↦ Fin.elim0 v)
  simpa using congrArg (fun K ↦ K x x) h

section PartitionBoundaryChecks

open Classical in
/-- The vacuum has one configuration even when the local alphabet is empty. -/
example (M : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ) (p q : Fin 0 → Prop) :
    Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd q (fun _ ↦ Fin 0))
          (Equiv.piEquivPiSubtypeProd q (fun _ ↦ Fin 0))) ≤
      Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd p (fun _ ↦ Fin 0))
          (Equiv.piEquivPiSubtypeProd p (fun _ ↦ Fin 0))) := by
  convert! Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le M p q using 1
  all_goals simp only [Fintype.card_unique, one_pow, one_mul]

/-- The generic predicate comparison also includes an empty local alphabet. -/
example (M : Matrix (Fin 1 → Fin 0) (Fin 1 → Fin 0) ℂ) :
    Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd (fun _ : Fin 1 ↦ False) (fun _ ↦ Fin 0))
          (Equiv.piEquivPiSubtypeProd (fun _ : Fin 1 ↦ False) (fun _ ↦ Fin 0))) ≤ 0 := by
  simpa [Matrix.operatorSchmidtRank_eq_finrank_operatorBlockSpan, Fintype.card_fun] using
    Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le M
      (fun _ ↦ True) (fun _ ↦ False)

/-- Exchanged regions with one and two binary sites give the generic cost 64. -/
example (M : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) :
    Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd (fun v : Fin 3 ↦ v ≠ 0) (fun _ ↦ Fin 2))
          (Equiv.piEquivPiSubtypeProd (fun v : Fin 3 ↦ v ≠ 0) (fun _ ↦ Fin 2))) ≤
      64 * Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd (fun v : Fin 3 ↦ v = 0) (fun _ ↦ Fin 2))
          (Equiv.piEquivPiSubtypeProd (fun v : Fin 3 ↦ v = 0) (fun _ ↦ Fin 2))) := by
  simpa [Matrix.operatorSchmidtRank_eq_finrank_operatorBlockSpan,
    Fintype.card_fun, Fintype.card_subtype_eq] using
    Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le M
      (fun v ↦ v = 0) (fun v ↦ v ≠ 0)

end PartitionBoundaryChecks
