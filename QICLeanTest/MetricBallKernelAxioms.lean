/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MetricBallKernel

/-! Raw-backed standard-axiom guards for finite-radius ball incidence kernels. -/

/--
info: 'Metric.ballIncidenceKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.ballIncidenceKernel

/--
info: 'Metric.ballIncidenceKernel_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.ballIncidenceKernel_nonneg

/--
info: 'Metric.edist_ne_top_and_toReal_le_two_mul_of_ball_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.edist_ne_top_and_toReal_le_two_mul_of_ball_bounds

/--
info: 'Metric.ballIncidenceKernel_eq_zero_of_edist_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.ballIncidenceKernel_eq_zero_of_edist_eq_top

/--
info: 'Metric.ballIncidenceKernel_le_card_labels' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.ballIncidenceKernel_le_card_labels

/--
info: 'Metric.sum_ballIncidenceKernel_mul_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Metric.sum_ballIncidenceKernel_mul_exp_le
