/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.JordanBlockDirectSum

/-!
Audit the finite genuine Jordan-sum milestone and its degenerate source
boundaries. In particular, a size-two zero block is nonzero at its first
positive power; the nilpotence theorem must start later.
-/

open scoped Matrix.Norms.L2Operator
open Matrix Filter

example : jordanBlock 2 0 ^ 1 ≠ 0 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ A 0 1) h
  rw [jordanBlock_pow_apply] at he
  norm_num at he

example : jordanBlock 2 0 ^ 2 = 0 := jordanBlock_zero_pow_eq_zero 2 2 le_rfl

example (n : ℕ) :
    ‖jordanBlockDirectSum (ι := Empty) (fun _ ↦ 1) (fun _ ↦ 0) ^ n‖ = 0 := by
  rw [jordanBlockDirectSum, ← blockDiagonal'_pow]
  exact l2_opNorm_blockDiagonal'_of_isEmpty (fun _ : Empty ↦ jordanBlock 1 0 ^ n)

example (n : ℕ) : ‖jordanBlock 1 0 ^ n‖ ≤ ‖jordanBlock 2 0 ^ n‖ :=
  l2_opNorm_jordanBlock_pow_le_of_norm_eq (by decide) 0 0 rfl n

example : ∀ᶠ n : ℕ in atTop, ‖jordanBlock 2 2 ^ n‖ < ‖jordanBlock 1 3 ^ n‖ := by
  apply eventually_l2_opNorm_jordanBlock_pow_lt_of_norm_lt
  norm_num

set_option linter.hashCommand false

#print axioms Matrix.blockDiagonal'StarAlgHom
#print axioms Matrix.l2_opNorm_blockDiagonal'
#print axioms Matrix.l2_opNNNorm_blockDiagonal'
#print axioms Matrix.l2_opNorm_block_le_blockDiagonal'
#print axioms Matrix.l2_opNorm_blockDiagonal'_eq_of_max
#print axioms Matrix.exists_l2_opNorm_blockDiagonal'_eq
#print axioms Matrix.l2_opNorm_blockDiagonal'_of_isEmpty
#print axioms Matrix.jordanBlock_pow_apply
#print axioms Matrix.jordanBlock_pow_submatrix_castLE
#print axioms Matrix.l2_opNorm_principal_submatrix_le
#print axioms Matrix.l2_opNorm_jordanBlock_pow_mono_dim
#print axioms Matrix.l2_opNorm_jordanBlock_pow_phase
#print axioms Matrix.l2_opNorm_jordanBlock_pow_norm
#print axioms Matrix.l2_opNorm_jordanBlock_pow_le_of_norm_eq
#print axioms Matrix.jordanBlock_zero_pow_eq_zero
#print axioms Matrix.eventually_l2_opNorm_jordanBlock_pow_lt_of_norm_lt
#print axioms Matrix.jordanBlockDirectSum
#print axioms Matrix.l2_opNNNorm_jordanBlockDirectSum_pow
#print axioms Matrix.exists_jordanBlock_maximal
#print axioms Matrix.eventually_l2_opNorm_jordanBlockDirectSum_pow_eq
#print axioms Matrix.jordanBlockDirectSum_zero_pow_eq_zero
#print axioms Matrix.jordanBlockDirectSum_pow_eq_zero_of_maximal_zero
#print axioms Matrix.le_l2_opNorm_jordanBlockDirectSum_pow_polynomial
#print axioms Matrix.eventually_l2_opNorm_jordanBlockDirectSum_pow_polynomial_bounds
#print axioms Matrix.exists_pos_eventually_jordanBlockDirectSum_pow_bounds
#print axioms Matrix.exists_pos_jordanBlockDirectSum_pow_le_polynomial
