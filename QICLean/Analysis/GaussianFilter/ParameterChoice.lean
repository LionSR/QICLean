/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed parameters for Gaussian error bounds

Given a positive gap `Δ` and a nonnegative real exponent `r`, constants `A > 0`
and `T₀ > 0` can be chosen before the buffer parameter `b` and the size `L`.
For every `b ≥ 0` and `L ≥ 1`, the choices `B = 1 + b + log L`, `h = A * B`,
and `T = T₀ * B` give spectral error at most `exp (-10 * b) * L ^ (-r)` and
Gaussian truncation error at most twice that quantity. In particular, the
power exponent is real and need not be an integer.

This is the scalar parameter choice in the polynomial-PEPS manuscript (2026),
`lem:reset`, `02-information.tex`, lines 443–452, at source revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It specializes the two
error expressions established in the local Gaussian filter modules. No
operator estimate, physical reset, or locality conclusion is asserted here.

The constants are constructed as `A = 2 * (30 + r) / Δ ^ 2` and
`T₀ = sqrt (2 * A * (30 + r))`. The proof reuses Mathlib's positive square
root, monotonicity of the exponential, and the logarithmic formula for real
powers. No OpenAI Lean proof text is copied or adapted.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

/-
Source: peps-02-information-adc7f124.tex, lines 443–452.
Reuse: Mathlib positive square root and ordered-field arithmetic.

Source: peps-02-information-adc7f124.tex, lines 443–452.
Reuse: Mathlib exponential monotonicity and positive-base real powers.

Source: peps-02-information-adc7f124.tex, lines 443–452.
Reuse: explicit fixed constants and scalar error bounds in this module.

Source: peps-02-information-adc7f124.tex, lines 425–452.
Reuse: the uniform parameter theorem with the manuscript exponent `2 * p + 10`.
-/

namespace GaussianFilter

/-- The fixed constants required in `02-information.tex`, `lem:reset`, lines
443–452, exist for any positive gap and nonnegative real error exponent. -/
theorem exists_gaussian_parameter_constants {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      30 + r ≤ A * Δ ^ 2 / 2 ∧ 30 + r ≤ T₀ ^ 2 / (2 * A) := by
  let A := 2 * (30 + r) / Δ ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hprod : 0 < 2 * A * (30 + r) := by positivity
  refine ⟨A, Real.sqrt (2 * A * (30 + r)), hA, Real.sqrt_pos.mpr hprod, ?_, ?_⟩
  · have heq : A * Δ ^ 2 / 2 = 30 + r := by
      dsimp [A]
      field_simp [hΔ.ne']
    exact heq.ge
  · rw [Real.sq_sqrt hprod.le]
    have heq : 2 * A * (30 + r) / (2 * A) = 30 + r :=
      mul_div_cancel_left₀ _ (mul_pos two_pos hA).ne'
    exact heq.ge

private theorem exp_neg_mul_log_scale_le {c r b L : ℝ} (hr : 0 ≤ r)
    (hb : 0 ≤ b) (hL : 1 ≤ L) (hc : 30 + r ≤ c) :
    Real.exp (-c * (1 + b + Real.log L)) ≤ Real.exp (-10 * b) * L ^ (-r) := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hcb : 10 * b ≤ c * b :=
    mul_le_mul_of_nonneg_right (by linarith) hb
  have hclog : r * Real.log L ≤ c * Real.log L :=
    mul_le_mul_of_nonneg_right (by linarith) hlog
  rw [Real.rpow_def_of_pos hLpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Any positive constants meeting the manuscript's two numerical conditions
give both Gaussian error bounds at every `b ≥ 0` and `L ≥ 1`; see
`02-information.tex`, `lem:reset`, lines 443–452. The variance is positive and
the cutoff is nonnegative, as required to apply the Gaussian estimates. -/
theorem gaussian_error_bounds_of_parameter_constants {Δ r A T₀ b L : ℝ}
    (hA : 0 < A) (hT₀ : 0 ≤ T₀) (hr : 0 ≤ r)
    (hgap : 30 + r ≤ A * Δ ^ 2 / 2) (htail : 30 + r ≤ T₀ ^ 2 / (2 * A))
    (hb : 0 ≤ b) (hL : 1 ≤ L) :
    let B := 1 + b + Real.log L
    let h := A * B
    let T := T₀ * B
    0 < h ∧ 0 ≤ T ∧
      Real.exp (-h * Δ ^ 2 / 2) ≤ Real.exp (-10 * b) * L ^ (-r) ∧
      2 * Real.exp (-T ^ 2 / (2 * h)) ≤ 2 * Real.exp (-10 * b) * L ^ (-r) := by
  let B := 1 + b + Real.log L
  have hB : 0 < B := by
    have hlog := Real.log_nonneg hL
    dsimp [B]
    linarith
  refine ⟨mul_pos hA hB, mul_nonneg hT₀ hB.le, ?_, ?_⟩
  · calc
      Real.exp (-(A * B) * Δ ^ 2 / 2) =
          Real.exp (-(A * Δ ^ 2 / 2) * B) := by congr 1; ring
      _ ≤ Real.exp (-10 * b) * L ^ (-r) :=
        exp_neg_mul_log_scale_le hr hb hL hgap
  · have hbound : Real.exp (-(T₀ * B) ^ 2 / (2 * (A * B))) ≤
        Real.exp (-10 * b) * L ^ (-r) := by
      calc
        Real.exp (-(T₀ * B) ^ 2 / (2 * (A * B))) =
            Real.exp (-(T₀ ^ 2 / (2 * A)) * B) := by
          congr 1
          field_simp [hA.ne', hB.ne']
        _ ≤ Real.exp (-10 * b) * L ^ (-r) :=
          exp_neg_mul_log_scale_le hr hb hL htail
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound (le_of_lt two_pos)

/-- Uniform scalar parameter choice from `02-information.tex`, `lem:reset`,
lines 443–452. The existential constants precede both universally quantified
scale variables, so neither constant depends on `b` or `L`. -/
theorem exists_gaussian_parameters {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      30 + r ≤ A * Δ ^ 2 / 2 ∧ 30 + r ≤ T₀ ^ 2 / (2 * A) ∧
      ∀ b L : ℝ, 0 ≤ b → 1 ≤ L →
        let B := 1 + b + Real.log L
        let h := A * B
        let T := T₀ * B
        0 < h ∧ 0 ≤ T ∧
          Real.exp (-h * Δ ^ 2 / 2) ≤ Real.exp (-10 * b) * L ^ (-r) ∧
          2 * Real.exp (-T ^ 2 / (2 * h)) ≤ 2 * Real.exp (-10 * b) * L ^ (-r) := by
  obtain ⟨A, T₀, hA, hT₀, hgap, htail⟩ := exists_gaussian_parameter_constants hΔ hr
  exact ⟨A, T₀, hA, hT₀, hgap, htail, fun _ _ hb hL ↦
    gaussian_error_bounds_of_parameter_constants hA hT₀.le hr hgap htail hb hL⟩

/-- The source's choice `r = 2 * p + 10`, with constants independent of the
buffer and system size; see `02-information.tex`, `lem:reset`, lines 425–452. -/
theorem exists_gaussian_parameters_of_polynomial_exponent {Δ p : ℝ}
    (hΔ : 0 < Δ) (hp : 0 ≤ p) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      30 + (2 * p + 10) ≤ A * Δ ^ 2 / 2 ∧
      30 + (2 * p + 10) ≤ T₀ ^ 2 / (2 * A) ∧
      ∀ b L : ℝ, 0 ≤ b → 1 ≤ L →
        let B := 1 + b + Real.log L
        let h := A * B
        let T := T₀ * B
        0 < h ∧ 0 ≤ T ∧
          Real.exp (-h * Δ ^ 2 / 2) ≤ Real.exp (-10 * b) * L ^ (-(2 * p + 10)) ∧
          2 * Real.exp (-T ^ 2 / (2 * h)) ≤
            2 * Real.exp (-10 * b) * L ^ (-(2 * p + 10)) :=
  exists_gaussian_parameters hΔ (by linarith)

end GaussianFilter
