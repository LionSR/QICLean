/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecay

/-! Foundational-axiom guards for every public finite-word declaration. -/

set_option linter.hashCommand false

/--
info: 'Matrix.contractionWord' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWord

/--
info: 'Matrix.contractionWord_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWord_zero

/--
info: 'Matrix.contractionWord_snoc' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWord_snoc

/--
info: 'Matrix.sqrt_one_sub_toEuclideanLin_eq_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.sqrt_one_sub_toEuclideanLin_eq_self

/--
info: 'Matrix.inner_sqrt_one_sub_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inner_sqrt_one_sub_eq_zero

/--
info: 'Matrix.norm_sq_sqrt_one_sub' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_sq_sqrt_one_sub

/--
info: 'Matrix.sum_norm_sq_sqrt_one_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.sum_norm_sq_sqrt_one_sub_le

/--
info: 'Matrix.eq_zero_of_card_lt_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.eq_zero_of_card_lt_gap

/--
info: 'Matrix.contractionWord_fix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWord_fix

/--
info: 'Matrix.inner_contractionWord_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inner_contractionWord_eq_zero

/--
info: 'Matrix.contractionWordSum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSum

/--
info: 'Matrix.contractionWordSum_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSum_zero

/--
info: 'Matrix.contractionWordSum_succ' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSum_succ

/--
info: 'Matrix.contractionWordSum_succ_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSum_succ_le

/--
info: 'Matrix.contractionWordSum_le_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.contractionWordSum_le_pow
