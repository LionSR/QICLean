/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecaySpectator

/-! Standard-axiom guards for every public spectator contraction-word declaration. -/

set_option linter.hashCommand false

/--
info: 'Matrix.kronecker_one_mulVec_apply_slice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.kronecker_one_mulVec_apply_slice

/--
info: 'Matrix.norm_sq_eq_sum_spectator_slices' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_sq_eq_sum_spectator_slices

/--
info: 'Matrix.norm_sq_toEuclideanLin_kronecker_one_eq_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_sq_toEuclideanLin_kronecker_one_eq_sum

/--
info: 'Matrix.contractionWord_snoc_kronecker_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWord_snoc_kronecker_one

/--
info: 'Matrix.contractionWordSpectatorSum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSpectatorSum

/--
info: 'Matrix.contractionWordSpectatorSum_eq_sum_slices' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSpectatorSum_eq_sum_slices

/--
info: 'Matrix.contractionWordSpectatorSum_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSpectatorSum_zero

/--
info: 'Matrix.contractionWordSpectatorSum_zero_vector' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSpectatorSum_zero_vector

/--
info: 'Matrix.contractionWordSpectatorSum_le_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSpectatorSum_le_pow

/--
info: 'Matrix.spectator_eq_zero_of_card_lt_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.spectator_eq_zero_of_card_lt_gap

/--
info: 'Matrix.inner_toEuclideanLin_one_sub_vecMulVec_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inner_toEuclideanLin_one_sub_vecMulVec_eq_zero

/--
info: 'Matrix.inner_spectatorSlice_excitedProjection_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inner_spectatorSlice_excitedProjection_eq_zero

/--
info: 'Matrix.contractionWordSpectatorSum_excitedProjection_le_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSpectatorSum_excitedProjection_le_pow

/--
info: 'Matrix.spectator_excitedProjection_eq_zero_of_card_lt_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.spectator_excitedProjection_eq_zero_of_card_lt_gap
