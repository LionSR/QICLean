/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StretchedExponentialSummability

/-! Raw-backed standard-axiom guards for stretched exponential moments and tails. -/

/--
info: 'Real.summable_nat_pow_mul_exp_neg_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.summable_nat_pow_mul_exp_neg_mul_rpow

/--
info: 'Real.one_le_tsum_nat_pow_mul_exp_neg_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.one_le_tsum_nat_pow_mul_exp_neg_mul_rpow

/--
info: 'Real.tsum_nat_pow_mul_exp_neg_mul_rpow_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.tsum_nat_pow_mul_exp_neg_mul_rpow_tail_le
