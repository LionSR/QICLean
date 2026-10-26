/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.UnitaryTraceZero

/-! # Axiom guards for permutation matrices and vanishing unitary trace pairings -/

/-- info:
'Equiv.Perm.permMatrix_mem_unitaryGroup' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Equiv.Perm.permMatrix_mem_unitaryGroup

/-- info:
'Matrix.IsHermitian.exists_unitary_trace_mul_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.IsHermitian.exists_unitary_trace_mul_eq_zero
