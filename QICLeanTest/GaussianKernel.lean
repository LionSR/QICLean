/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.Kernel
import Mathlib.Tactic.NormNum

/-! Regressions for variance, angular frequency, zero variance, and the closed-window tail. -/

open GaussianFilter MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace GaussianKernelTest

example : (∫ t, kernel 1 t) = 1 := integral_kernel one_ne_zero

example : kernel 1 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by simp [kernel_eq]

-- Variance two at angular frequency one gives exp(-1), with no Fourier factor 2π.
example : (∫ t : ℝ, (kernel 2 t : ℂ) * Complex.exp ((1 : ℂ) * t * Complex.I)) =
    Complex.exp (-1) := by
  convert integral_kernel_cexp (h := 2) (by norm_num) 1 using 1
  norm_num

example : (∫ t in (Icc (0 : ℝ) 0)ᶜ, kernel 1 t) ≤ 2 := by
  simpa using integral_kernel_compl_Icc_le (h := 1) one_ne_zero (T := 0) le_rfl

example : (gaussianReal 0 1).real (Icc (-2 : ℝ) 2)ᶜ ≤ 2 * Real.exp (-2) := by
  convert measure_compl_Icc_le 1 (T := 2) (by norm_num) using 1
  norm_num

-- The zero-variance probability is a Dirac mass, while the density is identically zero.
example : gaussianReal 0 0 = Measure.dirac 0 := gaussianReal_zero_var 0

example : (∫ t, kernel 0 t) = 0 := by simp

example (ω : ℝ) :
    (∫ t : ℝ, Complex.exp ((ω : ℂ) * t * Complex.I) ∂gaussianReal 0 0) = 1 := by
  rw [integral_cexp]
  simp

example : (gaussianReal 0 0).real (Icc (0 : ℝ) 0)ᶜ = 0 := by
  simp [measureReal_def]

end GaussianKernelTest

/--
info: 'GaussianFilter.kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.kernel

/--
info: 'GaussianFilter.kernel_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.kernel_eq

/--
info: 'GaussianFilter.kernel_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.kernel_nonneg

/--
info: 'GaussianFilter.integrable_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integrable_kernel

/--
info: 'GaussianFilter.integral_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integral_kernel

/--
info: 'GaussianFilter.kernel_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.kernel_zero

/--
info: 'GaussianFilter.integrable_kernel_smul_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integrable_kernel_smul_iff

/--
info: 'GaussianFilter.integral_kernel_smul' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integral_kernel_smul

/--
info: 'GaussianFilter.setIntegral_kernel_smul' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.setIntegral_kernel_smul

/--
info: 'GaussianFilter.integral_kernel_eq_measureReal' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integral_kernel_eq_measureReal

/--
info: 'GaussianFilter.integral_cexp' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integral_cexp

/--
info: 'GaussianFilter.integral_kernel_cexp' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integral_kernel_cexp

/--
info: 'GaussianFilter.hasSubgaussianMGF_gaussianReal' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.hasSubgaussianMGF_gaussianReal

/--
info: 'GaussianFilter.measure_compl_Icc_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.measure_compl_Icc_le

/--
info: 'GaussianFilter.integral_kernel_compl_Icc_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integral_kernel_compl_Icc_le
