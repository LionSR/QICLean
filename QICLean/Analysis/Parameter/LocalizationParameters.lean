/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform localization radius

For fixed `T₀ > 0`, `v ≥ 0`, `μ > 0`, and real `r ≥ 0`, choose
`K = (v * T₀ + 15 + r) / μ` before the buffer `b`, size `L`, and error
prefactor `C`. With `B = 1 + b + log L` and `ℓ = Nat.ceil (K * B)`, the
localization error `C * L ^ 4 * (1 + T₀ * B) * exp (v * T₀ * B - μ * ℓ)`
is at most `C * (1 + T₀) * exp (-10 * b) * L ^ (-r)` for every
`b ≥ 0`, `L ≥ 1`, and `C ≥ 0`.

This makes explicit the scalar absorption in the polynomial-PEPS manuscript
(September 24, 2026), `lem:reset`, `02-information.tex`, lines 546–554, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The fixed factor
`1 + T₀` is part of the source's unspecified constant. The natural ceiling
is positive and lies between `K * B` and `K * B + 1`. This module proves
only the scalar estimate; no localized operator or physical reset is assumed
or constructed.

The proof uses Mathlib's exponential inequalities, positive-base real powers,
and natural ceiling. No OpenAI Lean proof text is copied or adapted.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

/-
Source: peps-02-information-adc7f124.tex, lines 551–554.
Reuse: Mathlib ordered-field arithmetic.

Source: peps-02-information-adc7f124.tex, lines 546–554.
Reuse: Mathlib exponential inequalities, real powers, and natural ceiling.

Source: peps-02-information-adc7f124.tex, lines 546–554.
Reuse: the explicit coefficient and scalar estimate in this module.
-/

namespace GaussianFilter

/-- A fixed radius coefficient for the scalar localization estimate in
`02-information.tex`, `lem:reset`, lines 551–554. -/
theorem exists_localization_parameter_constant {T₀ v μ r : ℝ}
    (hT₀ : 0 ≤ T₀) (hv : 0 ≤ v) (hμ : 0 < μ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ v * T₀ + 15 + r ≤ μ * K := by
  let K := (v * T₀ + 15 + r) / μ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have heq : μ * K = v * T₀ + 15 + r := by
    dsimp [K]
    field_simp [hμ.ne']
  exact heq.ge

private theorem one_add_mul_le_exp {T B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) :
    1 + T * B ≤ (1 + T) * Real.exp B := by
  have hBexp : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  have hmul := mul_le_mul_of_nonneg_left hBexp hT
  have hone := Real.one_le_exp hB
  nlinarith

/-- Any coefficient satisfying the explicit numerical condition absorbs the
localization error in `02-information.tex`, `lem:reset`, lines 546–554.
The radius is rounded upward to a natural number, and the error prefactor
may be zero. The exponent `r` is an arbitrary nonnegative real. -/
theorem localization_error_bound_of_parameter_constant {T₀ v μ r K b L C : ℝ}
    (hT₀ : 0 ≤ T₀) (hμ : 0 ≤ μ) (hr : 0 ≤ r)
    (hcoef : v * T₀ + 15 + r ≤ μ * K)
    (hb : 0 ≤ b) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    let B := 1 + b + Real.log L
    let ℓ := Nat.ceil (K * B)
    C * L ^ 4 * (1 + T₀ * B) * Real.exp (v * T₀ * B - μ * ℓ) ≤
      C * (1 + T₀) * Real.exp (-10 * b) * L ^ (-r) := by
  let B := 1 + b + Real.log L
  let ℓ := Nat.ceil (K * B)
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hround : μ * (K * B) ≤ μ * (ℓ : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.le_ceil (K * B)) hμ
  have hcoefB := mul_le_mul_of_nonneg_right hcoef hB
  have hdecay : v * T₀ * B - μ * (ℓ : ℝ) ≤ -(15 + r) * B := by
    nlinarith
  have hexponent :
      4 * Real.log L + B + (v * T₀ * B - μ * (ℓ : ℝ)) ≤
        -10 * b + Real.log L * (-r) := by
    have hrb := mul_nonneg hr hb
    dsimp [B] at hdecay ⊢
    nlinarith
  have hlinear := one_add_mul_le_exp hT₀ hB
  have hpow : L ^ (4 : ℕ) = Real.exp (4 * Real.log L) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hLpos] using (Real.exp_nat_mul (Real.log L) 4).symm
  calc
    C * L ^ 4 * (1 + T₀ * B) * Real.exp (v * T₀ * B - μ * (ℓ : ℝ)) ≤
        C * L ^ 4 * ((1 + T₀) * Real.exp B) *
          Real.exp (v * T₀ * B - μ * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlinear (mul_nonneg hC (pow_nonneg hLpos.le 4)))
        (Real.exp_nonneg _)
    _ = C * (1 + T₀) *
        (Real.exp (4 * Real.log L) * Real.exp B *
          Real.exp (v * T₀ * B - μ * (ℓ : ℝ))) := by rw [← hpow]; ring
    _ = C * (1 + T₀) *
        Real.exp (4 * Real.log L + B + (v * T₀ * B - μ * (ℓ : ℝ))) := by
      rw [Real.exp_add (4 * Real.log L + B), Real.exp_add (4 * Real.log L) B]
    _ ≤ C * (1 + T₀) * Real.exp (-10 * b + Real.log L * (-r)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        (mul_nonneg hC (by linarith))
    _ = C * (1 + T₀) * Real.exp (-10 * b) * L ^ (-r) := by
      rw [Real.rpow_def_of_pos hLpos, Real.exp_add]
      ring

/-- Uniform localization radius from `02-information.tex`, `lem:reset`, lines
546–554. One positive `K` is chosen before all `b`, `L`, and `C`. The natural
radius is positive, its rounding error is less than one, and the resulting
localization error has exponential buffer decay and the prescribed real
polynomial exponent. -/
theorem exists_localization_parameters {T₀ v μ r : ℝ}
    (hT₀ : 0 < T₀) (hv : 0 ≤ v) (hμ : 0 < μ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ v * T₀ + 15 + r ≤ μ * K ∧
      ∀ b L C : ℝ, 0 ≤ b → 1 ≤ L → 0 ≤ C →
        let B := 1 + b + Real.log L
        let ℓ := Nat.ceil (K * B)
        0 < ℓ ∧ K * B ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) < K * B + 1 ∧
          C * L ^ 4 * (1 + T₀ * B) * Real.exp (v * T₀ * B - μ * ℓ) ≤
            C * (1 + T₀) * Real.exp (-10 * b) * L ^ (-r) := by
  obtain ⟨K, hK, hcoef⟩ := exists_localization_parameter_constant hT₀.le hv hμ hr
  refine ⟨K, hK, hcoef, fun b L C hb hL hC ↦ ?_⟩
  have hB : 0 < 1 + b + Real.log L := by
    have hlog := Real.log_nonneg hL
    linarith
  exact ⟨Nat.ceil_pos.mpr (mul_pos hK hB), Nat.le_ceil _,
    Nat.ceil_lt_add_one (mul_pos hK hB).le,
    localization_error_bound_of_parameter_constant hT₀.le hμ.le hr hcoef hb hL hC⟩

end GaussianFilter
