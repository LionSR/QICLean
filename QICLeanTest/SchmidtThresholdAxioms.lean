/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.SchmidtThreshold

/-! # Axiom check for trimming a bipartite vector at a threshold on its Schmidt coefficients -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.norm_inner_le_of_posSemidef_smul_one_sub_leftMarginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_inner_le_of_posSemidef_smul_one_sub_leftMarginal

/-- info:
'Matrix.PosSemidef.posSemidef_smul_one_sub_one_sub_spectralProjectionGE_mul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.posSemidef_smul_one_sub_one_sub_spectralProjectionGE_mul

/-- info:
'Matrix.posSemidef_smul_one_sub_leftMarginal_leftApply_one_sub'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.posSemidef_smul_one_sub_leftMarginal_leftApply_one_sub

/-- info:
'Matrix.norm_inner_leftApply_one_sub_spectralProjectionGE_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_inner_leftApply_one_sub_spectralProjectionGE_le

/-- info:
'Matrix.mul_rank_spectralProjectionGE_leftMarginal_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.mul_rank_spectralProjectionGE_leftMarginal_le

/-- info:
'Matrix.exists_mul_eq_mul_transpose_of_commute'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_mul_eq_mul_transpose_of_commute

/-- info:
'Matrix.exists_leftApply_spectralProjectionGE_eq_rightApply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_leftApply_spectralProjectionGE_eq_rightApply
