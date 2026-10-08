/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RestoringCoefficientBound

/-! Axiom dependencies of all public restoring coefficient bounds. -/

set_option linter.hashCommand false

/--
info: 'Matrix.PosSemidef.nonneg_of_eq_diagonal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.nonneg_of_eq_diagonal

/--
info: 'Matrix.PosSemidef.supportInv_eq_diagonal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportInv_eq_diagonal

/--
info: 'Matrix.PosSemidef.trace_mul_supportInv_mul_re' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.trace_mul_supportInv_mul_re

/--
info: 'Matrix.PosSemidef.selected_sum_sq_div_le_trace_mul_supportInv_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.selected_sum_sq_div_le_trace_mul_supportInv_mul

/--
info: 'Matrix.PosSemidef.trace_mul_supportInv_mul_re_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.trace_mul_supportInv_mul_re_le

/--
info: 'Matrix.PosSemidef.selected_sum_sq_div_le_trace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.selected_sum_sq_div_le_trace
