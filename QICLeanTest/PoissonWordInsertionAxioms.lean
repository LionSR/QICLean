/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordInsertion

/-! Standard-axiom guards for insertion into the actual Poissonized word measures. -/

/--
info: 'PoissonWord.lintegral_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_eq_tsum

/--
info: 'PoissonWord.lintegral_sum_marked_eq_tsum' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_sum_marked_eq_tsum

/--
info: 'PoissonWord.lintegral_insertion_eq_tsum' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_insertion_eq_tsum

/--
info: 'PoissonWord.lintegral_sum_marked' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_sum_marked

/--
info: 'PoissonWord.lintegral_sum_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_sum_prefix

/--
info: 'PoissonWord.lintegral_length' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.lintegral_length
