/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordWeightedGrowth

/-! Raw-backed standard-axiom guards for weighted Poisson growth. -/

/--
info: 'PoissonWord.sum_length_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.sum_length_succ

/--
info: 'PoissonWord.sum_length_succ_le_of_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.sum_length_succ_le_of_append_singleton

/--
info: 'PoissonWord.sum_length_le_pow_of_weighted_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.sum_length_le_pow_of_weighted_growth

/--
info: 'PoissonWord.integrable_and_integral_le_of_weighted_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_and_integral_le_of_weighted_growth

/--
info: 'PoissonWord.eq_zero_of_weighted_growth_of_profile_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.eq_zero_of_weighted_growth_of_profile_eq_zero
