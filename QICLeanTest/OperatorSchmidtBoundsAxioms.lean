/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtBounds

/-! # Axiom guards for algebraic bounds on operator Schmidt rank -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.operatorSchmidtRank_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_add_le

/-- info:
'Matrix.operatorSchmidtRank_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_smul_le

/-- info:
'Matrix.operatorSchmidtRank_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_sum_le

/-- info:
'Matrix.operatorSchmidtRank_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_mul_le

