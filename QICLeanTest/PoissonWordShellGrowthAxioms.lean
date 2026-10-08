/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordShellGrowth

/-! Raw-backed standard-axiom guard for the direct shell growth theorem. -/

/--
info: 'PoissonWord.integrable_and_integral_le_of_shell_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_and_integral_le_of_shell_growth
