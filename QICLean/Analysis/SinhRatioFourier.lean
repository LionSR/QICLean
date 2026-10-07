/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SinhRatioDensity
import QICLean.Analysis.RectangleSimplePoles
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The Fourier formula for the hyperbolic-sine ratio

For `0 < s < 1/2` and real `z`,
\[
  \frac{\sinh(sz)}{\sinh(z/2)} = \int_{\mathbb R} e^{iuz}\, m_s(u)\,du,
  \qquad m_s(u) = \frac{\sin 2\pi s}{\cosh 2\pi u + \cos 2\pi s}.
\]
The proof integrates `e^{iwz} m_s(w)` around the rectangle with corners `-R` and
`R + i`. The density is periodic with period `i`, so the top edge is `e^{-z}` times the
bottom edge; the vertical edges vanish as `R → ∞`; and the two simple poles
`i(1/2 - s)`, `i(1/2 + s)` in the strip contribute `e^{-(1/2-s)z} - e^{-(1/2+s)z}`.

## Main results

* `Complex.cosh_two_pi_mul_add_cos_eq_zero` — the zeros of `cosh(2πw) + cos(2πs)` in
  the strip `0 ≤ Im w ≤ 1`.
* `Complex.exists_continuousAt_div_sub_inv` — the local form of a simple pole of a
  quotient of entire functions.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.3 (`transport:fourier`), proof lines
  214--226. The proofs are written independently from the paper.
-/

open Real Filter Topology MeasureTheory Set
open scoped Interval

namespace Complex

/-- The real and imaginary parts of `cosh` at `x + iy`. -/
theorem cosh_ofReal_add_ofReal_mul_I (x y : ℝ) :
    cosh ((x : ℂ) + y * I) = ((Real.cosh x * Real.cos y : ℝ) : ℂ) +
      ((Real.sinh x * Real.sin y : ℝ) : ℂ) * I := by
  rw [cosh_add, cosh_mul_I, sinh_mul_I, ← ofReal_cosh, ← ofReal_sinh, ← ofReal_cos,
    ← ofReal_sin]
  push_cast; ring

/-- **The zeros of `cosh(2πw) + cos(2πs)` in the closed strip `0 ≤ Im w ≤ 1`** are the
two points `i(1/2 - s)` and `i(1/2 + s)`, for `0 < s < 1/2`. -/
theorem cosh_two_pi_mul_add_cos_eq_zero {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {w : ℂ}
    (h0 : 0 ≤ w.im) (h1 : w.im ≤ 1)
    (hψ : cosh (2 * Real.pi * w) + Real.cos (2 * Real.pi * s) = 0) :
    w = ((1 / 2 - s : ℝ) : ℂ) * I ∨ w = ((1 / 2 + s : ℝ) : ℂ) * I := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hsθ : 0 < Real.sin (2 * π * s) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hw : (2 * Real.pi * w : ℂ) = ((2 * π * w.re : ℝ) : ℂ) + ((2 * π * w.im : ℝ) : ℂ) * I := by
    conv_lhs => rw [← re_add_im w]
    push_cast; ring
  rw [hw, cosh_ofReal_add_ofReal_mul_I] at hψ
  have hre := congrArg re hψ
  have him := congrArg im hψ
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    zero_re, add_im, mul_im, zero_add, add_zero, zero_im] at hre him
  rcases mul_eq_zero.mp him with hsh | hsin
  · rw [Real.sinh_eq_zero] at hsh
    have hwre : w.re = 0 := by
      have : (2 * π) * w.re = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
    rw [hsh, Real.cosh_zero, one_mul] at hre
    have hcos : Real.cos (2 * π * w.im) = Real.cos (π - 2 * π * s) := by
      rw [Real.cos_pi_sub]; linarith
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hcos
    · -- `π - θ = 2kπ + 2πb`
      have hlin : 1 - 2 * s = 2 * k + 2 * w.im := by
        have : π * (1 - 2 * s) = π * (2 * k + 2 * w.im) := by linarith
        exact mul_left_cancel₀ pi_ne_zero this
      have hk0 : k = 0 := by
        have h1' : (k : ℝ) < 1 / 2 := by linarith [hs.1]
        have h2' : -1 < (k : ℝ) := by linarith [hs.2]
        have : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
        have : -1 < k := by exact_mod_cast h2'
        omega
      subst hk0
      left
      apply Complex.ext <;> simp [hwre]
      push_cast at hlin; linarith
    · -- `π - θ = 2kπ - 2πb`
      have hlin : 1 - 2 * s = 2 * k - 2 * w.im := by
        have : π * (1 - 2 * s) = π * (2 * k - 2 * w.im) := by linarith
        exact mul_left_cancel₀ pi_ne_zero this
      have hk1 : k = 1 := by
        have h1' : (0 : ℝ) < (k : ℝ) := by linarith [hs.2]
        have h2' : (k : ℝ) < 3 / 2 := by linarith [hs.1]
        have : 0 < k := by exact_mod_cast h1'
        have : k < 2 := by exact_mod_cast (show (k : ℝ) < 2 by linarith)
        omega
      subst hk1
      right
      apply Complex.ext <;> simp [hwre]
      push_cast at hlin; linarith
  · exfalso
    have hc2 : Real.cos (2 * π * w.im) ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq (2 * π * w.im); rw [hsin] at this; linarith
    have hcθ : Real.cos (2 * π * s) ^ 2 < 1 := by
      have := Real.sin_sq_add_cos_sq (2 * π * s); nlinarith
    have hch : 1 ≤ Real.cosh (2 * π * w.re) := Real.one_le_cosh _
    have : (Real.cosh (2 * π * w.re) * Real.cos (2 * π * w.im)) ^ 2 =
        Real.cos (2 * π * s) ^ 2 := by rw [show Real.cosh (2 * π * w.re) *
          Real.cos (2 * π * w.im) = -Real.cos (2 * π * s) by linarith]; ring
    rw [mul_pow, hc2, mul_one] at this
    nlinarith

/-- **Local form of a simple pole.** If `φ` and `ψ` are entire, `ψ p = 0` and
`ψ'(p) ≠ 0`, then `φ/ψ - (φ(p)/ψ'(p)) (w - p)⁻¹` agrees near `p` (away from `p`) with a
function continuous at `p`. -/
theorem exists_continuousAt_div_sub_inv {φ ψ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hψ : Differentiable ℂ ψ) {p : ℂ} (hp : ψ p = 0) (hd : deriv ψ p ≠ 0) :
    ∃ G : ℂ → ℂ, ContinuousAt G p ∧
      ∀ᶠ w in 𝓝[≠] p, φ w / ψ w - φ p / deriv ψ p * (w - p)⁻¹ = G w := by
  set D := dslope ψ p
  have hD : Differentiable ℂ D := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope Filter.univ_mem).mpr hψ.differentiableOn
  have hDp : D p = deriv ψ p := dslope_same ψ p
  have hV : {w | D w ≠ 0} ∈ 𝓝 p :=
    hD.continuous.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds (by rw [hDp]; exact hd))
  set h : ℂ → ℂ := fun w ↦ φ w / D w
  have hh : DifferentiableOn ℂ h {w | D w ≠ 0} := fun w hw ↦
    ((hφ w).div (hD w) hw).differentiableWithinAt
  refine ⟨dslope h p, ?_, ?_⟩
  · have := (differentiableOn_dslope hV).mpr hh
    exact (this.differentiableAt hV).continuousAt
  · filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with w hw hwp
    have hwp' : w - p ≠ 0 := sub_ne_zero.mpr hwp
    have hψw : ψ w = (w - p) * D w := by
      simp only [D]
      rw [dslope_of_ne _ hwp, slope_def_field, hp, sub_zero]
      field_simp
    rw [dslope_of_ne _ hwp, slope_def_field, hψw, ← hDp]
    simp only [h]
    have hw' : D w ≠ 0 := hw
    field_simp

end Complex
