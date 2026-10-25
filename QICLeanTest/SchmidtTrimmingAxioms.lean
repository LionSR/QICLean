/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.SchmidtTrimming

/-! # Axiom check for trimming a bipartite vector to its leading Schmidt terms -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.exists_isTrimmingProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_isTrimmingProjection

/-- info:
'Matrix.IsTrimmingProjection.norm_inner_le_re_inner_normalized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.norm_inner_le_re_inner_normalized

/-- info:
'Matrix.IsTrimmingProjection.norm_inner_sub_le_norm_inner_leftApply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.norm_inner_sub_le_norm_inner_leftApply

/-- info:
'Matrix.IsHermitian.commute_of_forall_trace_mul_re_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsHermitian.commute_of_forall_trace_mul_re_le

/-- info:
'Matrix.IsTrimmingProjection.norm_leftApply_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.norm_leftApply_le

/-- info:
'Matrix.IsTrimmingProjection.commute_leftMarginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.commute_leftMarginal

/-- info:
'Matrix.IsTrimmingProjection.exists_mul_eq_mul_transpose'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.exists_mul_eq_mul_transpose

/-- info:
'Matrix.IsTrimmingProjection.exists_leftApply_eq_rightApply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.exists_leftApply_eq_rightApply

/-- info:
'Matrix.schmidtRank_rightApply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.schmidtRank_rightApply_le

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

-- Trimming to `k` terms, for every `k` and every Schmidt-rank bound `D`, with the
-- trimming projection supplied by the existence theorem.
example (u v : EuclideanSpace ℂ (m × n)) (k D : ℕ)
    (hv : Matrix.HasSchmidtRankLE D (WithLp.ofLp v)) :
    ∃ P : Matrix m m ℂ, ‖inner ℂ u v‖ - ‖u‖ * ‖v‖ * √((D : ℝ) / (k + 1)) ≤
      ‖inner ℂ (Matrix.leftApply P u) v‖ := by
  obtain ⟨P, hP⟩ := Matrix.exists_isTrimmingProjection u k
  exact ⟨P, hP.norm_inner_sub_le_norm_inner_leftApply v hv⟩

end
