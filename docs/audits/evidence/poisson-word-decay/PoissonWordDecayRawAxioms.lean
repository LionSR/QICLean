/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PoissonContractionDecay

/-! Raw transitive axiom inventory for every named public declaration in the package. -/

#print axioms PoissonWord.Word
#print axioms PoissonWord.nil
#print axioms PoissonWord.weight
#print axioms PoissonWord.weight_nonneg
#print axioms PoissonWord.sum_weight
#print axioms PoissonWord.hasSum_one_weight
#print axioms PoissonWord.measure
#print axioms PoissonWord.isProbabilityMeasure
#print axioms PoissonWord.measure_length
#print axioms PoissonWord.map_length
#print axioms PoissonWord.measure_of_isEmpty
#print axioms PoissonWord.integrable_iff
#print axioms PoissonWord.integrable_iff_sum
#print axioms PoissonWord.integral_eq_tsum_sum
#print axioms PoissonWord.hasSum_weight_mul_pow
#print axioms PoissonWord.integrable_and_integral_le_of_sum_le_pow
#print axioms PoissonWord.measure_singleton
#print axioms PoissonWord.measure_zero
#print axioms PoissonWord.instMeasurableSpaceWord
#print axioms PoissonWord.instMeasurableSingletonClassWord
#print axioms Matrix.contractionWord
#print axioms Matrix.contractionWord_zero
#print axioms Matrix.contractionWord_snoc
#print axioms Matrix.sqrt_one_sub_toEuclideanLin_eq_self
#print axioms Matrix.inner_sqrt_one_sub_eq_zero
#print axioms Matrix.norm_sq_sqrt_one_sub
#print axioms Matrix.sum_norm_sq_sqrt_one_sub_le
#print axioms Matrix.eq_zero_of_card_lt_gap
#print axioms Matrix.contractionWord_fix
#print axioms Matrix.inner_contractionWord_eq_zero
#print axioms Matrix.contractionWordSum
#print axioms Matrix.contractionWordSum_zero
#print axioms Matrix.contractionWordSum_succ
#print axioms Matrix.contractionWordSum_succ_le
#print axioms Matrix.contractionWordSum_le_pow
#print axioms Matrix.kronecker_one_mulVec_apply_slice
#print axioms Matrix.norm_sq_eq_sum_spectator_slices
#print axioms Matrix.norm_sq_toEuclideanLin_kronecker_one_eq_sum
#print axioms Matrix.contractionWord_snoc_kronecker_one
#print axioms Matrix.contractionWordSpectatorSum
#print axioms Matrix.contractionWordSpectatorSum_eq_sum_slices
#print axioms Matrix.contractionWordSpectatorSum_zero
#print axioms Matrix.contractionWordSpectatorSum_zero_vector
#print axioms Matrix.contractionWordSpectatorSum_le_pow
#print axioms Matrix.spectator_eq_zero_of_card_lt_gap
#print axioms Matrix.inner_toEuclideanLin_one_sub_vecMulVec_eq_zero
#print axioms Matrix.inner_spectatorSlice_excitedProjection_eq_zero
#print axioms Matrix.contractionWordSpectatorSum_excitedProjection_le_pow
#print axioms Matrix.spectator_excitedProjection_eq_zero_of_card_lt_gap
#print axioms Matrix.poissonContractionWordEnergy
#print axioms Matrix.poissonContractionWordEnergy_integrable_and_le
#print axioms Matrix.poissonContractionWord_excitedProjection_decay
