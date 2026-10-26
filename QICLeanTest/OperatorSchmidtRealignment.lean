/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtRealignment

/-!
# Applications of the operator Schmidt matrix-rank identity

The identity on two two-dimensional factors has operator Schmidt rank one.
This differs from its ordinary matrix rank and checks the index pairing.
-/

open Matrix

example : operatorSchmidtRank (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 1 := by
  classical
  let f : Fin 2 × Fin 2 → ℂ := fun ij ↦ if ij.1 = ij.2 then 1 else 0
  have hC : (fun (ij : Fin 2 × Fin 2) (kl : Fin 2 × Fin 2) ↦
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (ij.1, kl.1) (ij.2, kl.2)) =
        Matrix.vecMulVec f f := by
    ext ⟨i, j⟩ ⟨k, l⟩
    by_cases hi : i = j <;> by_cases hk : k = l <;>
      simp [Matrix.one_apply, Matrix.vecMulVec, f, hi, hk]
  have hle : operatorSchmidtRank (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1 := by
    rw [operatorSchmidtRank_eq_rank_realignment, hC]
    exact Matrix.rank_vecMulVec_le f f
  have hpos := operatorSchmidtRank_pos_of_ne_zero _
    (show (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≠ 0 by
      intro h
      have he := congrFun (congrFun h (0, 0)) (0, 0)
      norm_num at he)
  omega

/-- info:
'Matrix.operatorSchmidtRank_eq_rank_realignment' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_eq_rank_realignment
