/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordOccupation

/-! Standard-axiom guards for occupation of retained prefixes at omitted letters. -/

/--
info: 'PoissonWord.lintegral_sum_partition_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_sum_partition_prefix

/--
info: 'PoissonWord.lintegral_sum_omitted_partition_prefix' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_sum_omitted_partition_prefix

/--
info: 'PoissonWord.lintegral_omitted_count' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_omitted_count
