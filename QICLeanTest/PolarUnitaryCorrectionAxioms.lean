/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrection

/-! Axiom dependencies of the polar-correction theorems. -/

set_option linter.hashCommand false

/--
info: 'Matrix.PosSemidef.norm_le_norm_add_toEuclideanCLM' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.norm_le_norm_add_toEuclideanCLM

/--
info: 'Matrix.PosSemidef.norm_sub_le_add_residuals' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.norm_sub_le_add_residuals

/--
info: 'Matrix.PosSemidef.norm_one_sub_le_norm_one_sub_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.norm_one_sub_le_norm_one_sub_sq

/--
info: 'Matrix.norm_unitary_sub_le_add_residuals_of_mul_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_unitary_sub_le_add_residuals_of_mul_posSemidef

/--
info: 'Matrix.exists_unitary_polar_correction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_unitary_polar_correction
