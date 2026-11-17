/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.DetailedBalance

/-! Regression and kernel audit for Wolf's infimum and detailed-balance bounds. -/

open Matrix
open scoped Matrix.Norms.L2Operator

-- A diagonal matrix attains condition one, without any spectral restriction.
example (a : Fin 3 → ℂ) : jordanConditionNumber (diagonal a) = 1 := by
  have hf : (1 : ℝ) ∈ jordanConditionFactors (diagonal a) := by
    refine ⟨1, 1, diagonal a, by simp, by simp, isJordanMatrix_diagonal a, by simp, ?_⟩
    simp
  exact le_antisymm (by
    simpa using jordanConditionNumber_le (diagonal a) 1 1 (diagonal a)
      (by simp) (by simp) (isJordanMatrix_diagonal a) (by simp))
    (one_le_jordanConditionNumber _ ⟨1, hf⟩)

-- Genuine nontrivial nilpotent blocks belong to the admissible family too.
example : IsJordanMatrix (jordanBlockDirectSum (fun _ : Fin 1 ↦ 2) (fun _ ↦ 0)) :=
  isJordanMatrix_jordanBlockDirectSum 1 _ _ (by intro i; norm_num)

-- The zero-dimensional convention differs from the nonempty lower bound.
example : jordanConditionNumber (0 : Matrix (Fin 0) (Fin 0) ℂ) = 0 :=
  jordanConditionNumber_of_isEmpty _

set_option linter.hashCommand false

#print axioms Matrix.IsJordanMatrix
#print axioms Matrix.isJordanMatrix_jordanBlockDirectSum
#print axioms Matrix.isJordanMatrix_diagonal
#print axioms Matrix.jordanConditionFactors
#print axioms Matrix.jordanConditionNumber
#print axioms Matrix.bddBelow_jordanConditionFactors
#print axioms Matrix.jordanConditionNumber_le
#print axioms Matrix.one_le_jordanConditionNumber
#print axioms Matrix.jordanConditionNumber_of_isEmpty
#print axioms Matrix.exists_jordanConditionFactor_lt
#print axioms Matrix.jordanConditionNumber_bounds
#print axioms Matrix.l2_opNorm_pow_jordanConditionNumber_bounds
#print axioms Matrix.one_le_l2_opNorm_mul_of_mul_eq_one
#print axioms Matrix.exists_pos_pow_similarity_jordanBlockDirectSum_bounds
#print axioms Matrix.pow_eq_zero_of_similarity_jordanBlockDirectSum_maximal_zero
#print axioms Matrix.l2_opNorm_transpose
#print axioms Matrix.l2_opNorm_kronecker_one
#print axioms Matrix.l2_opNorm_kronecker_le
#print axioms Matrix.PosDef.jordanConditionNumber_le_of_detailedBalance
#print axioms jordanConditionNumber_transferMatrix_le_of_detailedBalance
#print axioms conditionFactor_transferMatrix_sigmaSandwich_le
#print axioms jordanConditionNumber_transferMatrix_le_of_sigmaSandwich
#print axioms fixedPoint_of_detailedBalance_sigmaSandwich
