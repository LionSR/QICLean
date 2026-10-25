/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.WeightedFrequencySchmidtRank

/-! # Axiom guard for weighted original-frequency sums -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.operatorSchmidtRank_middle_sum_smul_full_counts_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_middle_sum_smul_full_counts_le
