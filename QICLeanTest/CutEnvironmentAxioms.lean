/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CutEnvironment

/-! # Axiom check for cut coordinates with an environment factor -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Entropy.cutEnvVector_leftApply_of_cutOperator_eq_kronecker_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.cutEnvVector_leftApply_of_cutOperator_eq_kronecker_one

/-- info:
'Entropy.cutEnvVector_leftApply_localLift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.cutEnvVector_leftApply_localLift

/-- info:
'Entropy.cutEnvVector_leftApply_of_cutOperator_eq_one_kronecker'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.cutEnvVector_leftApply_of_cutOperator_eq_one_kronecker

/-- info:
'Entropy.IsSupportedOn.schmidtRank_cutEnvVector_leftApply_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.IsSupportedOn.schmidtRank_cutEnvVector_leftApply_le

/-- info:
'Entropy.cutEnvVector_rightApply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.cutEnvVector_rightApply

/-- info:
'Entropy.schmidtRank_cutEnvVector_rightApply_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.schmidtRank_cutEnvVector_rightApply_le

/-- info:
'Entropy.schmidtRank_cutVector_slice_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.schmidtRank_cutVector_slice_le
