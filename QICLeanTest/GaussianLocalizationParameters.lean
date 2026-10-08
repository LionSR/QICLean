/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.LocalizationParameters
import Mathlib.Tactic.NormNum

/-!
# Consumers of the uniform localization radius

The fixture `T₀ = v = 1`, `μ = 2`, `r = 1 / 2`, and `K = 33 / 4` meets
the coefficient condition with equality. Its ceiling at `b = 0`, `L = 1`
is `9`. The examples also cover a zero prefactor, the exponent endpoint,
and use of a single coefficient at two scales.
-/

open GaussianFilter

namespace GaussianLocalizationParametersTest

-- A real exponent strictly between zero and one and a noninteger coefficient.
example (b L C : ℝ) (hb : 0 ≤ b) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    let B := 1 + b + Real.log L
    C * L ^ 4 * (1 + B) *
        Real.exp (B - 2 * (Nat.ceil ((33 / 4 : ℝ) * B) : ℝ)) ≤
      C * 2 * Real.exp (-10 * b) * L ^ (-(1 / 2 : ℝ)) := by
  simpa [show (1 : ℝ) + 1 = 2 by norm_num] using
    localization_error_bound_of_parameter_constant
    (T₀ := 1) (v := 1) (μ := 2) (r := (1 / 2 : ℝ)) (K := 33 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb hL hC

-- Rounding genuinely increases the real radius at the smallest allowed scale.
private theorem fixture_ceiling : Nat.ceil (33 / 4 : ℝ) = 9 :=
  (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)

example : Nat.ceil (33 / 4 : ℝ) = 9 := fixture_ceiling

-- Both scale endpoints, with the natural ceiling explicitly evaluated.
example (C : ℝ) (hC : 0 ≤ C) :
    C * 2 * Real.exp (-17) ≤ C * 2 := by
  have h := localization_error_bound_of_parameter_constant
    (T₀ := 1) (v := 1) (μ := 2) (r := (1 / 2 : ℝ)) (K := 33 / 4)
    (b := 0) (L := 1) (C := C)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hC
  norm_num [fixture_ceiling] at h
  exact h

-- The coefficient theorem can be used when C = 0, without a strict-positivity input.
example {T₀ v μ r K b L : ℝ} (hT₀ : 0 ≤ T₀) (hμ : 0 ≤ μ) (hr : 0 ≤ r)
    (hcoef : v * T₀ + 15 + r ≤ μ * K) (hb : 0 ≤ b) (hL : 1 ≤ L) :
    let B := 1 + b + Real.log L
    (0 : ℝ) * L ^ 4 * (1 + T₀ * B) *
        Real.exp (v * T₀ * B - μ * (Nat.ceil (K * B) : ℝ)) ≤
      0 * (1 + T₀) * Real.exp (-10 * b) * L ^ (-r) :=
  localization_error_bound_of_parameter_constant hT₀ hμ hr hcoef hb hL (le_refl 0)

-- The exponent endpoint r = 0 still gives exponential decay at all sizes.
example (b L C : ℝ) (hb : 0 ≤ b) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    let B := 1 + b + Real.log L
    C * L ^ 4 * (1 + B) * Real.exp (B - 2 * (Nat.ceil (8 * B) : ℝ)) ≤
      C * 2 * Real.exp (-10 * b) := by
  simpa [show (1 : ℝ) + 1 = 2 by norm_num] using
    localization_error_bound_of_parameter_constant
    (T₀ := 1) (v := 1) (μ := 2) (r := 0) (K := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb hL hC

-- The same K controls two different scales and error prefactors.
example : ∃ K : ℝ, 0 < K ∧
    0 < Nat.ceil K ∧ K ≤ (Nat.ceil K : ℝ) ∧ (Nat.ceil K : ℝ) < K + 1 ∧
    2 * Real.exp (1 - (Nat.ceil K : ℝ)) ≤ 2 ∧
    3 * (4 : ℝ) ^ 4 * (1 + (3 + Real.log 4)) *
        Real.exp (3 + Real.log 4 - (Nat.ceil (K * (3 + Real.log 4)) : ℝ)) ≤
      6 * Real.exp (-20) * (4 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, _, hscale⟩ := exists_localization_parameters
    (T₀ := 1) (v := 1) (μ := 1) (r := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfirst := hscale 0 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hsecond := hscale 2 4 3 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hfirst hsecond
  refine ⟨K, hK, ?_, hfirst.2.1, hfirst.2.2.1, ?_, ?_⟩
  · simpa using hfirst.1
  · convert hfirst.2.2.2 using 1
    norm_num
  · convert hsecond.2.2.2 using 1 <;> norm_num

end GaussianLocalizationParametersTest

/--
info: 'GaussianFilter.exists_localization_parameter_constant' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_localization_parameter_constant

/--
info: 'GaussianFilter.localization_error_bound_of_parameter_constant' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.localization_error_bound_of_parameter_constant

/--
info: 'GaussianFilter.exists_localization_parameters' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_localization_parameters
