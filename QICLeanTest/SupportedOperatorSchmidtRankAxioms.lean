/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SupportedOperatorSchmidtRank

/-! # Axiom guards for operator Schmidt rank from designated supports -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le

/-- info:
'Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
