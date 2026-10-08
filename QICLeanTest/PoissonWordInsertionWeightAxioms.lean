/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordInsertionWeight

/-! Foundational-axiom guards for the insertion-time weight declarations. -/

/--
info: 'PoissonWord.continuous_weight_ofReal' depends on axioms: [propext, Classical.choice,
  Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.continuous_weight_ofReal

/--
info: 'PoissonWord.measurable_weight_ofReal' depends on axioms: [propext, Classical.choice,
  Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.measurable_weight_ofReal

/--
info: 'PoissonWord.weight_mul_weight_nonneg' depends on axioms: [propext, Classical.choice,
  Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.weight_mul_weight_nonneg

/--
info: 'PoissonWord.intervalIntegrable_weight_mul_weight' depends on axioms: [propext,
  Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.intervalIntegrable_weight_mul_weight

/--
info: 'PoissonWord.integral_weight_mul_weight' depends on axioms: [propext, Classical.choice,
  Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integral_weight_mul_weight

/--
info: 'PoissonWord.lintegral_weight_mul_weight' depends on axioms: [propext, Classical.choice,
  Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_weight_mul_weight
