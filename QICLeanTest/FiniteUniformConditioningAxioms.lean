/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.FiniteUniformConditioning

/-! Standard-axiom audit for all finite equal-atom conditioning declarations. -/

/--
info: 'ProbabilityTheory.measure_eq_count_mul_of_finite_constant_singletons' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measure_eq_count_mul_of_finite_constant_singletons

/--
info: 'ProbabilityTheory.restrict_eq_smul_count_of_finite_constant_singletons' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.restrict_eq_smul_count_of_finite_constant_singletons

/--
info: 'ProbabilityTheory.cond_eq_uniformOn_of_finite_constant_singletons' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.cond_eq_uniformOn_of_finite_constant_singletons
