/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StretchedBallKernel

/-! Raw-backed standard-axiom guards for the convergent shell kernel. -/

/--
info: 'Metric.stretchedBallKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.stretchedBallKernel

/--
info: 'Metric.stretchedBallKernel_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.stretchedBallKernel_nonneg

/--
info: 'Metric.stretchedBallKernel_eq_zero_of_edist_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.stretchedBallKernel_eq_zero_of_edist_eq_top

/--
info: 'Metric.summable_stretchedBallKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.summable_stretchedBallKernel

/--
info: 'Metric.sum_stretchedBallKernel_mul_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.sum_stretchedBallKernel_mul_exp_le

/--
info: 'Metric.sum_stretchedBallKernel_mul_exp_half_rate_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.sum_stretchedBallKernel_mul_exp_half_rate_le
