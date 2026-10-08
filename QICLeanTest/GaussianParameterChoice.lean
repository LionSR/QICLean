/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.ParameterChoice

/-!
# Consumers of the uniform Gaussian parameter choice

The explicit fixture `Δ = 1`, `r = 1 / 2`, `A = T₀ = 61` attains both
coefficient thresholds exactly. It tests a noninteger power and the allowed
endpoints `L = 1` and `b = 0`. The existential consumer applies the same two
constants at distinct scales, checking their quantifier order.
-/

open GaussianFilter

namespace GaussianParameterChoiceTest

-- The size endpoint retains exponential decay in the buffer, with no `L > 1` input.
example (b : ℝ) (hb : 0 ≤ b) :
    Real.exp (-(61 * (1 + b)) / 2) ≤ Real.exp (-10 * b) ∧
      2 * Real.exp (-(61 * (1 + b)) ^ 2 / (2 * (61 * (1 + b)))) ≤
        2 * Real.exp (-10 * b) := by
  have h := gaussian_error_bounds_of_parameter_constants
    (Δ := 1) (r := (1 / 2 : ℝ)) (A := 61) (T₀ := 61) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hb (by norm_num)
  simpa using h.2.2

-- Zero buffer retains polynomial decay, with a real exponent strictly between 0 and 1.
example (L : ℝ) (hL : 1 ≤ L) :
    Real.exp (-(61 * (1 + Real.log L)) / 2) ≤ L ^ (-(1 / 2 : ℝ)) ∧
      2 * Real.exp (-(61 * (1 + Real.log L)) ^ 2 /
        (2 * (61 * (1 + Real.log L)))) ≤ 2 * L ^ (-(1 / 2 : ℝ)) := by
  have h := gaussian_error_bounds_of_parameter_constants
    (Δ := 1) (r := (1 / 2 : ℝ)) (A := 61) (T₀ := 61) (b := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hL
  simpa using h.2.2

-- Both endpoints are included simultaneously, with positive variance and cutoff.
example : 0 < (61 : ℝ) ∧ 0 ≤ (61 : ℝ) ∧
    Real.exp (-(61 / 2 : ℝ)) ≤ 1 ∧ 2 * Real.exp (-(61 / 2 : ℝ)) ≤ 2 := by
  have h := gaussian_error_bounds_of_parameter_constants
    (Δ := 1) (r := (1 / 2 : ℝ)) (A := 61) (T₀ := 61) (b := 0) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h ⊢

-- The same constants serve two different scales; choosing them after `b` or `L`
-- would not supply this consumer directly.
example {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      Real.exp (-A * Δ ^ 2 / 2) ≤ 1 ∧
      Real.exp (-(A * (3 + Real.log 4)) * Δ ^ 2 / 2) ≤
        Real.exp (-20) * (4 : ℝ) ^ (-(1 / 2 : ℝ)) ∧
      2 * Real.exp (-(T₀ * (3 + Real.log 4)) ^ 2 /
        (2 * (A * (3 + Real.log 4)))) ≤
          2 * Real.exp (-20) * (4 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, T₀, hA, hT₀, _, _, hscale⟩ :=
    exists_gaussian_parameters hΔ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hfirst := hscale 0 1 (by norm_num) (by norm_num)
  have hsecond := hscale 2 4 (by norm_num) (by norm_num)
  refine ⟨A, T₀, hA, hT₀, ?_, ?_, ?_⟩
  · simpa using hfirst.2.2.1
  · norm_num at hsecond ⊢
    exact hsecond.2.2.1
  · norm_num at hsecond ⊢
    exact hsecond.2.2.2

-- The lower endpoint `r = 0` still has constants uniform in both scale variables.
example {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      ∀ b L : ℝ, 0 ≤ b → 1 ≤ L →
        Real.exp (-(A * (1 + b + Real.log L)) * Δ ^ 2 / 2) ≤
          Real.exp (-10 * b) := by
  obtain ⟨A, T₀, hA, hT₀, _, _, hscale⟩ :=
    exists_gaussian_parameters hΔ (le_refl (0 : ℝ))
  refine ⟨A, T₀, hA, hT₀, fun b L hb hL ↦ ?_⟩
  simpa using (hscale b L hb hL).2.2.1

end GaussianParameterChoiceTest

/--
info: 'GaussianFilter.exists_gaussian_parameter_constants' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_gaussian_parameter_constants

/--
info: 'GaussianFilter.gaussian_error_bounds_of_parameter_constants' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussian_error_bounds_of_parameter_constants

/--
info: 'GaussianFilter.exists_gaussian_parameters' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_gaussian_parameters

/--
info: 'GaussianFilter.exists_gaussian_parameters_of_polynomial_exponent' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_gaussian_parameters_of_polynomial_exponent
