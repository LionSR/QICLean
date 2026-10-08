/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordJump

/-! Raw-backed standard-axiom guards for every public jump declaration. -/

/-- info: 'PoissonWord.take_succ_eq_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.take_succ_eq_append_singleton

/-- info: 'PoissonWord.sum_prefix_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.sum_prefix_increment

/-- info: 'PoissonWord.integrable_of_abs_le_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.integrable_of_abs_le_const

/-- info: 'PoissonWord.integrable_sum_prefix_of_abs_le_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.integrable_sum_prefix_of_abs_le_const

/-- info: 'PoissonWord.measurable_integral_of_abs_le_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.measurable_integral_of_abs_le_const

/-- info: 'PoissonWord.integrableOn_sum_word_integral_of_abs_le_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.integrableOn_sum_word_integral_of_abs_le_const

/-- info: 'PoissonWord.integral_sum_prefix_of_abs_le_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.integral_sum_prefix_of_abs_le_const

/-- info: 'PoissonWord.integral_sub_eq_integral_sum_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.integral_sub_eq_integral_sum_increment

/-- info: 'PoissonWord.integral_le_add_integral_sum_of_increment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonWord.integral_le_add_integral_sum_of_increment_le
