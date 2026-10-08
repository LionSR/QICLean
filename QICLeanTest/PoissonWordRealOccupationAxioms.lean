/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordRealOccupation

/-! Raw-backed standard-axiom guards for integrable real prefix occupation. -/

/--
info: 'PoissonWord.integrable_length' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_length

/--
info: 'PoissonWord.integral_length' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integral_length

/--
info: 'PoissonWord.integrable_of_nonneg_le_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_of_nonneg_le_const

/--
info: 'PoissonWord.measurable_integral_of_nonneg_le_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.measurable_integral_of_nonneg_le_const

/--
info: 'PoissonWord.integrable_sum_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_sum_prefix

/--
info: 'PoissonWord.integrableOn_sum_word_integral' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrableOn_sum_word_integral

/--
info: 'PoissonWord.integral_sum_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integral_sum_prefix

/--
info: 'PoissonWord.integrable_sum_partition_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_sum_partition_prefix

/--
info: 'PoissonWord.integral_sum_partition_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integral_sum_partition_prefix

/--
info: 'PoissonWord.integrable_sum_omitted_partition_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_sum_omitted_partition_prefix

/--
info: 'PoissonWord.integral_sum_omitted_partition_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integral_sum_omitted_partition_prefix
