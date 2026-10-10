/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TypicalTailScales

/-! Standard-axiom expectations for the linear and logarithmic typical-tail estimates. -/

/--
info: 'Entropy.exists_typical_tail_bound_of_linear_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.exists_typical_tail_bound_of_linear_budget

/--
info: 'Entropy.typicalWidth_div_sqrt_log_pow_twelve_budget_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.typicalWidth_div_sqrt_log_pow_twelve_budget_ge

/--
info: 'Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget
