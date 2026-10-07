/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.UnitaryEvolution

/-! Axiom dependencies of the unitary-evolution laws. -/

set_option linter.hashCommand false

/--
info: 'MatrixEvolution.hasDerivAt_star_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.hasDerivAt_star_mul

/--
info: 'MatrixEvolution.mem_unitaryGroup_of_hasDerivAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.mem_unitaryGroup_of_hasDerivAt

/--
info: 'MatrixEvolution.star_mul_sub_one_eq_integral' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.star_mul_sub_one_eq_integral

/--
info: 'MatrixEvolution.norm_sub_le_abs_integral_norm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.norm_sub_le_abs_integral_norm

/--
info: 'MatrixEvolution.norm_sub_le_of_generator_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.norm_sub_le_of_generator_bound
