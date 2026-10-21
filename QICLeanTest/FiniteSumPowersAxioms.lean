/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FiniteSumPowers

/-! # Axiom guard for the ordered expansion of a finite-sum power -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Fintype.sum_pow_eq_sum_ordered_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.sum_pow_eq_sum_ordered_words

/-- info:
'Fintype.smul_sub_average_pow_eq_sum_ordered_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.smul_sub_average_pow_eq_sum_ordered_words
