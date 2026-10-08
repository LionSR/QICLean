/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SupportInverseSandwich

/-! Axiom dependencies of the singular support-inverse order theorems. -/

set_option linter.hashCommand false

/--
info: 'Matrix.PosSemidef.mulVec_eq_zero_of_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.mulVec_eq_zero_of_le

/--
info: 'Matrix.PosSemidef.mul_supportProj_eq_self_of_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.mul_supportProj_eq_self_of_le

/--
info: 'Matrix.PosSemidef.supportProj_mul_eq_self_of_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportProj_mul_eq_self_of_le

/--
info: 'Matrix.PosSemidef.supportInvSqrt_mul_mul_supportInvSqrt_le_supportProj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportInvSqrt_mul_mul_supportInvSqrt_le_supportProj

/--
info: 'Matrix.PosSemidef.sub_mul_supportInv_mul_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.sub_mul_supportInv_mul_eq

/--
info: 'Matrix.PosSemidef.sub_mul_supportInv_mul_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.sub_mul_supportInv_mul_posSemidef

/--
info: 'Matrix.PosSemidef.mul_supportInv_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.mul_supportInv_mul_le
