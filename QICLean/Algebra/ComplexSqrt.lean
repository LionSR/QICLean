/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Basic.Complex.Basic

/-!
# Real square roots in the complex numbers

This file records the square identity for the complex coercion of a nonnegative
real square root, together with the companion identity for the square of its
inverse, and names the complex numbers `1 / √x` and `1 / √2` with their basic identities.

## Main definitions

* `Complex.invSqrt`: the complex number `1 / √x` of a real number `x`.
* `Complex.invSqrtTwo`: the complex number `1 / √2`, an abbreviation for `invSqrt 2`.

The declarations are ported from `TNLean/Algebra/ComplexSqrt.lean` at commit
`4150a33bacefe5ca311874b20cc4b90237fa447e` (Apache-2.0), with statements and names unchanged;
`Complex.invSqrt` and its identities are new here, and the identities of `Complex.invSqrtTwo` are
now their instances at `2`.
-/

namespace Complex

/-- The complex coercion of the real square root of a nonnegative number squares
to that number. -/
theorem ofReal_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ) ^ 2 = x := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]

/-- The inverse of the complex coercion of the real square root of a nonnegative
number multiplied by itself is the inverse of that number. -/
theorem ofReal_sqrt_inv_mul_self (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ)⁻¹ * (↑(Real.sqrt x) : ℂ)⁻¹ = (x : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- The complex number `1 / √x` of a real number `x`. -/
noncomputable def invSqrt (x : ℝ) : ℂ := ((Real.sqrt x : ℝ) : ℂ)⁻¹

theorem invSqrt_ne_zero {x : ℝ} (hx : 0 < x) : invSqrt x ≠ 0 :=
  inv_ne_zero (ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hx))

theorem invSqrt_mul_self {x : ℝ} (hx : 0 ≤ x) : invSqrt x * invSqrt x = (x : ℂ)⁻¹ :=
  ofReal_sqrt_inv_mul_self x hx

theorem invSqrt_sq {x : ℝ} (hx : 0 ≤ x) : invSqrt x ^ 2 = (x : ℂ)⁻¹ := by
  rw [pow_two, invSqrt_mul_self hx]

theorem norm_invSqrt_sq {x : ℝ} (hx : 0 ≤ x) : ‖invSqrt x‖ ^ 2 = x⁻¹ := by
  rw [invSqrt, _root_.norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x), inv_pow, Real.sq_sqrt hx]

theorem invSqrt_pow_mul_self {x : ℝ} (hx : 0 < x) (n : ℕ) :
    invSqrt x ^ n * invSqrt x ^ n * (x : ℂ) ^ n = 1 := by
  rw [← mul_pow, ← mul_pow, invSqrt_mul_self hx.le,
    inv_mul_cancel₀ (ofReal_ne_zero.2 hx.ne'), one_pow]

/-- `1 / √(xⁿ) = (1 / √x)ⁿ` for `x ≥ 0`. -/
theorem invSqrt_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : invSqrt (x ^ n) = invSqrt x ^ n := by
  induction n with
  | zero => simp [invSqrt]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [invSqrt]
    rw [Real.sqrt_mul (pow_nonneg hx n), ofReal_mul, mul_inv]

theorem invSqrt_mul_sqrt {x : ℝ} (hx : 0 < x) : invSqrt x * (↑(Real.sqrt x) : ℂ) = 1 :=
  inv_mul_cancel₀ (ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hx))

theorem sqrt_mul_invSqrt {x : ℝ} (hx : 0 < x) : (↑(Real.sqrt x) : ℂ) * invSqrt x = 1 :=
  mul_inv_cancel₀ (ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hx))

/-- The complex number `1 / √x` is real, so complex conjugation fixes it. -/
@[simp] theorem conj_invSqrt (x : ℝ) : starRingEnd ℂ (invSqrt x) = invSqrt x := by
  simp [invSqrt, Complex.conj_ofReal]

/-- The `star` spelling of `conj_invSqrt`. -/
@[simp] theorem star_invSqrt (x : ℝ) : star (invSqrt x) = invSqrt x := by
  simp [invSqrt, Complex.conj_ofReal]

/-- The complex number `1 / √2`, the normalization of a Hadamard-type factor. -/
noncomputable abbrev invSqrtTwo : ℂ := invSqrt 2

/-- The complex number `1 / √2` is nonzero. -/
theorem invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 := invSqrt_ne_zero two_pos

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  rw [invSqrt_mul_self zero_le_two, ofReal_ofNat]

/-- The square of `1 / √2` is `1 / 2`. -/
theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = (2 : ℂ)⁻¹ := by
  rw [invSqrt_sq zero_le_two, ofReal_ofNat]

/-- The squared norm of `1 / √2` is `1 / 2`. -/
theorem norm_invSqrtTwo_sq : ‖invSqrtTwo‖ ^ 2 = 2⁻¹ := norm_invSqrt_sq zero_le_two

theorem invSqrtTwo_pow_mul_self (n : ℕ) :
    invSqrtTwo ^ n * invSqrtTwo ^ n * (2 : ℂ) ^ n = 1 := by
  rw [← invSqrt_pow_mul_self two_pos n, ofReal_ofNat]

/-- The complex number `1 / √2` times the complex coercion of `√2` is one. -/
theorem invSqrtTwo_mul_sqrtTwo : invSqrtTwo * (↑(Real.sqrt 2) : ℂ) = 1 := invSqrt_mul_sqrt two_pos

/-- The complex coercion of `√2` times the complex number `1 / √2` is one. -/
theorem sqrtTwo_mul_invSqrtTwo : (↑(Real.sqrt 2) : ℂ) * invSqrtTwo = 1 := sqrt_mul_invSqrt two_pos

/-- The complex number `1 / √2` is real, so complex conjugation fixes it. -/
@[simp] theorem conj_invSqrtTwo : starRingEnd ℂ invSqrtTwo = invSqrtTwo := conj_invSqrt 2

/-- The `star` spelling of `conj_invSqrtTwo`, for rewriting after
`Matrix.conjTranspose_smul`. -/
@[simp] theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := star_invSqrt 2

end Complex
