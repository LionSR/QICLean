/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTrimming

/-! # Axiom check for the trimming of a viable subspace -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.mul_spectralProjectionGE_leftMarginal_of_leftApply_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.mul_spectralProjectionGE_leftMarginal_of_leftApply_eq

/-- info:
'Matrix.inner_leftApply_left'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inner_leftApply_left

/-- info:
'Matrix.inner_rightApply_left'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inner_rightApply_left

/-- info:
'Matrix.norm_rightApply_sq_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_rightApply_sq_le

/-- info:
'Entropy.trimProj_props'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.trimProj_props

/-- info:
'Entropy.trimProj_mul_trimProj_of_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.trimProj_mul_trimProj_of_le

/-- info:
'Entropy.trimDiff_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.trimDiff_eq

/-- info:
'Entropy.sum_norm_leftApply_trimDiff_sq_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.sum_norm_leftApply_trimDiff_sq_le

/-- info:
'Entropy.eq_rightApply_stackVector'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.eq_rightApply_stackVector

/-- info:
'Entropy.norm_inner_leftApply_trimDiff_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.norm_inner_leftApply_trimDiff_le

/-- info:
'Entropy.leftApply_trimProj_mem_prodExt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.leftApply_trimProj_mem_prodExt

/-- info:
'Entropy.isCloseTo_prodExt_trimSubspace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.isCloseTo_prodExt_trimSubspace

/-- info:
'Entropy.schmidtRank_cutVector_trimmed_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.schmidtRank_cutVector_trimmed_le
