/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.MatrixIntegral

/-! Standard-axiom guards for every public two-generator Gaussian matrix declaration. -/

/--
info: 'GaussianFilter.gaussianIntertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner

/--
info: 'GaussianFilter.gaussianIntertwinerTruncated' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwinerTruncated

/--
info: 'GaussianFilter.continuous_intertwinerIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.continuous_intertwinerIntegrand

/--
info: 'GaussianFilter.norm_intertwinerIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_intertwinerIntegrand

/--
info: 'GaussianFilter.integrable_intertwinerIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integrable_intertwinerIntegrand

/--
info: 'GaussianFilter.integrable_intertwinerIntegrand_restrict' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integrable_intertwinerIntegrand_restrict

/--
info: 'GaussianFilter.norm_gaussianIntertwiner_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwiner_le

/--
info: 'GaussianFilter.norm_gaussianIntertwinerTruncated_le_mass' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwinerTruncated_le_mass

/--
info: 'GaussianFilter.norm_gaussianIntertwinerTruncated_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwinerTruncated_le

/--
info: 'GaussianFilter.norm_gaussianIntertwiner_sub_truncated_le_mass' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwiner_sub_truncated_le_mass

/--
info: 'GaussianFilter.norm_gaussianIntertwiner_sub_truncated_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwiner_sub_truncated_le

/--
info: 'GaussianFilter.gaussianIntertwiner_eq_integral_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_eq_integral_kernel

/--
info: 'GaussianFilter.gaussianIntertwinerTruncated_eq_integral_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwinerTruncated_eq_integral_kernel

/--
info: 'GaussianFilter.integrable_kernel_intertwinerIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integrable_kernel_intertwinerIntegrand

/--
info: 'GaussianFilter.gaussianIntertwiner_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_conjTranspose

/--
info: 'GaussianFilter.gaussianIntertwinerTruncated_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwinerTruncated_conjTranspose

/--
info: 'GaussianFilter.gaussianIntertwiner_zero_variance' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_zero_variance

/--
info: 'GaussianFilter.gaussianIntertwiner_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_zero

/--
info: 'GaussianFilter.dotProduct_intertwinerIntegrand_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.dotProduct_intertwinerIntegrand_mulVec

/--
info: 'GaussianFilter.dotProduct_gaussianIntertwiner_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.dotProduct_gaussianIntertwiner_mulVec

/--
info: 'GaussianFilter.inner_gaussianIntertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.inner_gaussianIntertwiner
