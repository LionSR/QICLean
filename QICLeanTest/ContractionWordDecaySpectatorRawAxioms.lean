/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecaySpectator

/-! Raw axiom inventory for every public spectator contraction-word declaration. -/

set_option linter.hashCommand false

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
