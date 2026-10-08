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

section Strip

variable {s : ℝ}

/-- The denominator `cosh(2πw) + cos(2πs)` of the density. -/
noncomputable def densityDenom (s : ℝ) (w : ℂ) : ℂ :=
  cosh (2 * Real.pi * w) + Real.cos (2 * Real.pi * s)

/-- The integrand `e^{iwz} m_s(w)` of the Fourier integral. -/
noncomputable def fourierIntegrand (s z : ℝ) (w : ℂ) : ℂ :=
  cexp (I * w * z) * sinhRatioDensity s w

theorem fourierIntegrand_eq (s z : ℝ) (w : ℂ) :
    fourierIntegrand s z w = cexp (I * w * z) * Real.sin (2 * Real.pi * s) / densityDenom s w := by
  rw [fourierIntegrand, sinhRatioDensity, densityDenom, mul_div_assoc]

theorem differentiable_densityDenom (s : ℝ) : Differentiable ℂ (densityDenom s) := by
  unfold densityDenom; fun_prop

theorem deriv_densityDenom (s : ℝ) (w : ℂ) :
    deriv (densityDenom s) w = 2 * Real.pi * sinh (2 * Real.pi * w) := by
  unfold densityDenom
  have h := ((Complex.hasDerivAt_cosh _).comp w ((hasDerivAt_id w).const_mul
    (2 * (Real.pi : ℂ)))).add_const ((Real.cos (2 * Real.pi * s) : ℝ) : ℂ)
  rw [show (fun w : ℂ ↦ cosh (2 * Real.pi * w) + ((Real.cos (2 * Real.pi * s) : ℝ) : ℂ)) =
    fun x ↦ (cosh ∘ fun y ↦ 2 * (Real.pi : ℂ) * id y) x + ((Real.cos (2 * Real.pi * s) : ℝ) : ℂ)
    from rfl, h.deriv]
  simp; ring

/-- The first pole `i(1/2 - s)`. -/
noncomputable def pole₁ (s : ℝ) : ℂ := ((1 / 2 - s : ℝ) : ℂ) * I

/-- The second pole `i(1/2 + s)`. -/
noncomputable def pole₂ (s : ℝ) : ℂ := ((1 / 2 + s : ℝ) : ℂ) * I

theorem densityDenom_pole₁ (s : ℝ) : densityDenom s (pole₁ s) = 0 := by
  have : (2 * (Real.pi : ℂ) * pole₁ s) = ((Real.pi - 2 * Real.pi * s : ℝ) : ℂ) * I := by
    rw [pole₁]; push_cast; ring
  rw [densityDenom, this, cosh_mul_I, ← ofReal_cos, Real.cos_pi_sub]; push_cast; ring

theorem densityDenom_pole₂ (s : ℝ) : densityDenom s (pole₂ s) = 0 := by
  have : (2 * (Real.pi : ℂ) * pole₂ s) = ((Real.pi + 2 * Real.pi * s : ℝ) : ℂ) * I := by
    rw [pole₂]; push_cast; ring
  rw [densityDenom, this, cosh_mul_I, ← ofReal_cos, show Real.pi + 2 * Real.pi * s =
    2 * Real.pi * s + Real.pi by ring, Real.cos_add_pi]; push_cast; ring

end Strip

theorem pole₁_ne_pole₂ {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) : pole₁ s ≠ pole₂ s := by
  intro h
  have := congrArg im h
  simp [pole₁, pole₂] at this
  linarith [hs.1]

theorem deriv_densityDenom_pole₁ (s : ℝ) :
    deriv (densityDenom s) (pole₁ s) = 2 * Real.pi * (Real.sin (2 * Real.pi * s) * I) := by
  rw [deriv_densityDenom]
  have : (2 * (Real.pi : ℂ) * pole₁ s) = ((Real.pi - 2 * Real.pi * s : ℝ) : ℂ) * I := by
    rw [pole₁]; push_cast; ring
  rw [this, sinh_mul_I, ← ofReal_sin, Real.sin_pi_sub]

theorem deriv_densityDenom_pole₂ (s : ℝ) :
    deriv (densityDenom s) (pole₂ s) = -(2 * Real.pi * (Real.sin (2 * Real.pi * s) * I)) := by
  rw [deriv_densityDenom]
  have : (2 * (Real.pi : ℂ) * pole₂ s) = ((Real.pi + 2 * Real.pi * s : ℝ) : ℂ) * I := by
    rw [pole₂]; push_cast; ring
  rw [this, sinh_mul_I, ← ofReal_sin, show Real.pi + 2 * Real.pi * s =
    2 * Real.pi * s + Real.pi by ring, Real.sin_add_pi]
  push_cast; ring

/-- The numerator `e^{iwz} sin(2πs)` of the integrand. -/
noncomputable def fourierNumer (s z : ℝ) (w : ℂ) : ℂ :=
  cexp (I * w * z) * Real.sin (2 * Real.pi * s)

theorem differentiable_fourierNumer (s z : ℝ) : Differentiable ℂ (fourierNumer s z) := by
  unfold fourierNumer; fun_prop

/-- The residue coefficient at a pole. -/
noncomputable def residueCoeff (s z : ℝ) (p : ℂ) : ℂ :=
  fourierNumer s z p / deriv (densityDenom s) p

theorem two_pi_I_mul_residues {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ) :
    2 * Real.pi * I * (residueCoeff s z (pole₁ s) + residueCoeff s z (pole₂ s)) =
      cexp (-((1 / 2 - s : ℝ) * z)) - cexp (-((1 / 2 + s : ℝ) * z)) := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : (Real.sin (2 * Real.pi * s) : ℂ) ≠ 0 := by
    exact_mod_cast (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  rw [residueCoeff, residueCoeff, deriv_densityDenom_pole₁, deriv_densityDenom_pole₂,
    fourierNumer, fourierNumer, pole₁, pole₂]
  have e1 : I * (((1 / 2 - s : ℝ) : ℂ) * I) * z = -((1 / 2 - s : ℝ) * z) := by
    ring_nf; rw [I_sq]; ring
  have e2 : I * (((1 / 2 + s : ℝ) : ℂ) * I) * z = -((1 / 2 + s : ℝ) * z) := by
    ring_nf; rw [I_sq]; ring
  rw [e1, e2]
  generalize ((Real.sin (2 * Real.pi * s) : ℝ) : ℂ) = S at hS ⊢
  field_simp
  ring

theorem fourierIntegrand_eq_div (s z : ℝ) (w : ℂ) :
    fourierIntegrand s z w = fourierNumer s z w / densityDenom s w := by
  rw [fourierIntegrand_eq, fourierNumer]

/-- The denominator does not vanish in the closed strip away from the two poles. -/
theorem densityDenom_ne_zero {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {w : ℂ} (h0 : 0 ≤ w.im)
    (h1 : w.im ≤ 1) (hw₁ : w ≠ pole₁ s) (hw₂ : w ≠ pole₂ s) : densityDenom s w ≠ 0 := fun h ↦
  (cosh_two_pi_mul_add_cos_eq_zero hs h0 h1 h).elim hw₁ hw₂

/-- **The rectangle identity.** For `R > 0` the boundary integral of `e^{iwz} m_s(w)` over the
rectangle with corners `-R` and `R + i` is `e^{-(1/2-s)z} - e^{-(1/2+s)z}`.

Area-law paper, proof of Lemma 7.3 (`transport:fourier`), `06-transport.tex`
lines 215--223. -/
theorem rectBoundaryIntegral_fourierIntegrand {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ)
    {R : ℝ} (hR : 0 < R) :
    rectBoundaryIntegral (fourierIntegrand s z) (-(R : ℂ)) (R + I) =
      cexp (-((1 / 2 - s : ℝ) * z)) - cexp (-((1 / 2 + s : ℝ) * z)) := by
  have hne := pole₁_ne_pole₂ hs
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : (Real.sin (2 * Real.pi * s) : ℂ) ≠ 0 := by
    exact_mod_cast (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hp₁im : (pole₁ s).im = 1 / 2 - s := by simp [pole₁]
  have hp₂im : (pole₂ s).im = 1 / 2 + s := by simp [pole₂]
  have hp₁re : (pole₁ s).re = 0 := by simp [pole₁]
  have hp₂re : (pole₂ s).re = 0 := by simp [pole₂]
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (show (2 * Real.pi) ≠ 0 by positivity)
  have hd₁ : deriv (densityDenom s) (pole₁ s) ≠ 0 := by
    rw [deriv_densityDenom_pole₁]; exact mul_ne_zero h2pi (mul_ne_zero hS I_ne_zero)
  have hd₂ : deriv (densityDenom s) (pole₂ s) ≠ 0 := by
    rw [deriv_densityDenom_pole₂]
    exact neg_ne_zero.mpr (mul_ne_zero h2pi (mul_ne_zero hS I_ne_zero))
  obtain ⟨G₁, hG₁c, hG₁⟩ := exists_continuousAt_div_sub_inv (differentiable_fourierNumer s z)
    (differentiable_densityDenom s) (densityDenom_pole₁ s) hd₁
  obtain ⟨G₂, hG₂c, hG₂⟩ := exists_continuousAt_div_sub_inv (differentiable_fourierNumer s z)
    (differentiable_densityDenom s) (densityDenom_pole₂ s) hd₂
  set p₁ := pole₁ s
  set p₂ := pole₂ s
  set c₁ := residueCoeff s z p₁
  set c₂ := residueCoeff s z p₂
  set P : Finset ℂ := {p₁, p₂}
  set c : ℂ → ℂ := fun p ↦ if p = p₁ then c₁ else c₂
  have hsum : ∀ u, ∑ p ∈ P, c p * (u - p)⁻¹ = c₁ * (u - p₁)⁻¹ + c₂ * (u - p₂)⁻¹ := by
    intro u; rw [Finset.sum_pair hne]; simp [c, Ne.symm hne]
  set F : ℂ → ℂ := fun u ↦ fourierIntegrand s z u - (c₁ * (u - p₁)⁻¹ + c₂ * (u - p₂)⁻¹)
  -- Local forms at the poles.
  set g : ℂ → ℂ := Function.update (Function.update F p₁ (G₁ p₁ - c₂ * (p₁ - p₂)⁻¹)) p₂
    (G₂ p₂ - c₁ * (p₂ - p₁)⁻¹)
  have hgF : ∀ u, u ≠ p₁ → u ≠ p₂ → g u = F u := fun u h1 h2 ↦ by
    simp only [g, Function.update_of_ne h2, Function.update_of_ne h1]
  have hfdiv : fourierIntegrand s z = fun w ↦ fourierNumer s z w / densityDenom s w :=
    funext (fourierIntegrand_eq_div s z)
  have hrect : ∀ u : ℂ, u ∈ [[(-(R : ℂ)).re, ((R : ℂ) + I).re]] ×ℂ
      [[(-(R : ℂ)).im, ((R : ℂ) + I).im]] → 0 ≤ u.im ∧ u.im ≤ 1 := by
    intro u hu
    simp only [mem_reProdIm, neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, I_re,
      add_zero, add_im, I_im, zero_add, uIcc_of_le zero_le_one, mem_Icc] at hu
    exact hu.2
  -- Continuity of the regular part on the closed rectangle.
  have hpole_cont : ∀ (q : ℂ) (u : ℂ), u ≠ q → ∀ (a : ℂ),
      ContinuousAt (fun w ↦ a * (w - q)⁻¹) u := fun q u hu a ↦
    continuousAt_const.mul ((continuousAt_id.sub_const q).inv₀ (sub_ne_zero.mpr hu))
  have hgc : ContinuousOn g ([[(-(R : ℂ)).re, ((R : ℂ) + I).re]] ×ℂ
      [[(-(R : ℂ)).im, ((R : ℂ) + I).im]]) := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    obtain ⟨h0, h1⟩ := hrect u hu
    by_cases hu₁ : u = p₁
    · subst hu₁
      have hev : ∀ᶠ w in 𝓝 p₁, g w = G₁ w - c₂ * (w - p₂)⁻¹ := by
        have h2 : ∀ᶠ w in 𝓝 p₁, w ≠ p₂ := isOpen_ne.mem_nhds hne
        have h3 := eventually_nhdsWithin_iff.mp hG₁
        filter_upwards [h2, h3] with w hw2 hw3
        by_cases hw1 : w = p₁
        · subst hw1; simp [g, Function.update_of_ne hne]
        · rw [hgF w hw1 hw2, ← hw3 hw1]
          simp only [F, fourierIntegrand_eq_div, c₁, c₂, residueCoeff]; ring
      exact (hG₁c.sub (hpole_cont p₂ p₁ hne c₂)).congr (hev.mono fun w hw ↦ hw.symm)
    by_cases hu₂ : u = p₂
    · subst hu₂
      have hev : ∀ᶠ w in 𝓝 p₂, g w = G₂ w - c₁ * (w - p₁)⁻¹ := by
        have h2 : ∀ᶠ w in 𝓝 p₂, w ≠ p₁ := isOpen_ne.mem_nhds (Ne.symm hne)
        have h3 := eventually_nhdsWithin_iff.mp hG₂
        filter_upwards [h2, h3] with w hw1 hw3
        by_cases hw2 : w = p₂
        · subst hw2; simp [g]
        · rw [hgF w hw1 hw2, ← hw3 hw2]
          simp only [F, fourierIntegrand_eq_div, c₁, c₂, residueCoeff]; ring
      exact (hG₂c.sub (hpole_cont p₁ p₂ (Ne.symm hne) c₁)).congr (hev.mono fun w hw ↦ hw.symm)
    · have hev : ∀ᶠ w in 𝓝 u, g w = F w := by
        filter_upwards [isOpen_ne.mem_nhds hu₁, isOpen_ne.mem_nhds hu₂] with w hw1 hw2
        exact hgF w hw1 hw2
      refine ContinuousAt.congr ?_ (hev.mono fun w hw ↦ hw.symm)
      have hd := densityDenom_ne_zero hs h0 h1 hu₁ hu₂
      refine ContinuousAt.sub ?_ ((hpole_cont p₁ u hu₁ c₁).add (hpole_cont p₂ u hu₂ c₂))
      rw [hfdiv]
      exact ((differentiable_fourierNumer s z).continuous.continuousAt).div
        ((differentiable_densityDenom s).continuous.continuousAt) hd
  have hP : ∀ p ∈ P, ((-(R : ℂ)).re < p.re ∧ p.re < ((R : ℂ) + I).re) ∧
      ((-(R : ℂ)).im < p.im ∧ p.im < ((R : ℂ) + I).im) := by
    intro p hp
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp
    simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, I_re, add_zero, add_im,
      I_im, zero_add]
    rcases hp with rfl | rfl
    · rw [hp₁re, hp₁im]; exact ⟨⟨by linarith, hR⟩, by linarith [hs.2], by linarith [hs.1]⟩
    · rw [hp₂re, hp₂im]; exact ⟨⟨by linarith, hR⟩, by linarith [hs.1], by linarith [hs.2]⟩
  have hg : ∀ u ∈ [[(-(R : ℂ)).re, ((R : ℂ) + I).re]] ×ℂ [[(-(R : ℂ)).im, ((R : ℂ) + I).im]],
      u ∉ P → g u = fourierIntegrand s z u - ∑ p ∈ P, c p * (u - p)⁻¹ := by
    intro u _ hu
    simp only [P, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    rw [hsum, hgF u hu.1 hu.2]
  have hfd : ∀ u ∈ Ioo (min (-(R : ℂ)).re ((R : ℂ) + I).re) (max (-(R : ℂ)).re ((R : ℂ) + I).re)
      ×ℂ Ioo (min (-(R : ℂ)).im ((R : ℂ) + I).im) (max (-(R : ℂ)).im ((R : ℂ) + I).im),
      u ∉ P → DifferentiableAt ℂ (fourierIntegrand s z) u := by
    intro u hu huP
    simp only [P, Finset.mem_insert, Finset.mem_singleton, not_or] at huP
    simp only [mem_reProdIm, neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, I_re,
      add_zero, add_im, I_im, zero_add, mem_Ioo] at hu
    have h0 : 0 ≤ u.im := by have := hu.2.1; simp at this; linarith
    have h1 : u.im ≤ 1 := by have := hu.2.2; simp at this; linarith
    rw [hfdiv]
    exact (differentiable_fourierNumer s z u).div (differentiable_densityDenom s u)
      (densityDenom_ne_zero hs h0 h1 huP.1 huP.2)
  rw [integral_boundary_rect_eq_of_simple_poles P c hP hg hgc hfd, Finset.sum_pair hne]
  have hc₁ : c p₁ = c₁ := by simp [c]
  have hc₂ : c p₂ = c₂ := by simp [c, Ne.symm hne]
  rw [hc₁, hc₂]
  exact two_pi_I_mul_residues hs z

/-- `‖cosh(a + ib)‖ ≥ |sinh a|`. -/
theorem abs_sinh_le_norm_cosh (a b : ℝ) : |Real.sinh a| ≤ ‖cosh ((a : ℂ) + b * I)‖ := by
  rw [cosh_ofReal_add_ofReal_mul_I, norm_def, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [normSq_apply]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_im, mul_im, zero_add, add_zero]
  have h1 := Real.cosh_sq a
  have h2 := Real.sin_sq_add_cos_sq b
  nlinarith [sq_nonneg (Real.cos b), sq_nonneg (Real.sinh a)]

/-- The density is periodic with period `i`. -/
theorem densityDenom_add_I (s : ℝ) (w : ℂ) : densityDenom s (w + I) = densityDenom s w := by
  rw [densityDenom, densityDenom, mul_add, cosh_add]
  have h1 : cosh (2 * (Real.pi : ℂ) * I) = 1 := by
    rw [cosh_mul_I, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_cos, Real.cos_two_pi, ofReal_one]
  have h2 : sinh (2 * (Real.pi : ℂ) * I) = 0 := by
    rw [sinh_mul_I, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_sin, Real.sin_two_pi, ofReal_zero,
      zero_mul]
  rw [h1, h2]; ring

/-- On the top edge the integrand is `e^{-z}` times the integrand on the real line. -/
theorem fourierIntegrand_add_I (s z : ℝ) (x : ℝ) :
    fourierIntegrand s z ((x : ℂ) + I) = cexp (-(z : ℂ)) * fourierIntegrand s z x := by
  rw [fourierIntegrand_eq, fourierIntegrand_eq, densityDenom_add_I]
  have : I * ((x : ℂ) + I) * z = I * x * z + -(z : ℂ) := by ring_nf; rw [I_sq]; ring
  rw [this, Complex.exp_add]; ring

/-- On the real line the integrand has modulus `m_s(x)`. -/
theorem norm_fourierIntegrand_ofReal (s z x : ℝ) :
    ‖fourierIntegrand s z x‖ = |Real.sinhRatioDensity s x| := by
  rw [fourierIntegrand, norm_mul]
  have h1 : ‖cexp (I * x * z)‖ = 1 := by
    rw [show I * (x : ℂ) * z = ((x * z : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  have h2 : sinhRatioDensity s x = (Real.sinhRatioDensity s x : ℂ) := by
    simp only [sinhRatioDensity, Real.sinhRatioDensity]
    push_cast; rfl
  rw [h1, one_mul, h2, norm_real, Real.norm_eq_abs]

/-- The integrand is integrable on the real line. -/
theorem integrable_fourierIntegrand {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ) :
    Integrable (fun x : ℝ ↦ fourierIntegrand s z x) := by
  have hcont : Continuous (fun x : ℝ ↦ fourierIntegrand s z x) := by
    have hfdiv : (fun x : ℝ ↦ fourierIntegrand s z x) =
        fun x : ℝ ↦ fourierNumer s z x / densityDenom s x := funext fun x ↦
      fourierIntegrand_eq_div s z x
    rw [hfdiv]
    refine ((differentiable_fourierNumer s z).continuous.comp continuous_ofReal).div
      ((differentiable_densityDenom s).continuous.comp continuous_ofReal) fun x ↦ ?_
    exact densityDenom_ne_zero hs (by simp) (by simp)
      (fun h ↦ by have := congrArg im h; simp [pole₁] at this; linarith [hs.2])
      (fun h ↦ by have := congrArg im h; simp [pole₂] at this; linarith [hs.1])
  refine (Real.integrable_sinhRatioDensity hs).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_fourierIntegrand_ofReal, abs_of_pos (Real.sinhRatioDensity_pos hs x)]

/-- The bound on a vertical edge. -/
theorem norm_fourierIntegrand_vertical_le {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ)
    {x y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hx : 1 < Real.sinh (2 * π * |x|)) :
    ‖fourierIntegrand s z ((x : ℂ) + y * I)‖ ≤
      Real.exp |z| * (Real.sin (2 * π * s) / (Real.sinh (2 * π * |x|) - 1)) := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : 0 < Real.sin (2 * π * s) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [fourierIntegrand, norm_mul]
  have hexp : ‖cexp (I * ((x : ℂ) + y * I) * z)‖ ≤ Real.exp |z| := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have : (I * ((x : ℂ) + y * I) * z).re = -(y * z) := by simp
    rw [this]
    have h1 : |y * z| ≤ |z| := by
      rw [abs_mul, abs_of_nonneg hy0]; exact mul_le_of_le_one_left (abs_nonneg z) hy1
    linarith [neg_abs_le (y * z)]
  have hden : Real.sinh (2 * π * |x|) - 1 ≤ ‖densityDenom s ((x : ℂ) + y * I)‖ := by
    have h1 := abs_sinh_le_norm_cosh (2 * π * x) (2 * π * y)
    rw [Real.abs_sinh, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h1
    have h2 : ‖((Real.cos (2 * π * s) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    have heq : (2 * (Real.pi : ℂ) * ((x : ℂ) + y * I)) =
        ((2 * π * x : ℝ) : ℂ) + ((2 * π * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [densityDenom, heq]
    have := norm_sub_norm_le (cosh (((2 * π * x : ℝ) : ℂ) + ((2 * π * y : ℝ) : ℂ) * I))
      (-((Real.cos (2 * π * s) : ℝ) : ℂ))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hmS : ‖sinhRatioDensity s ((x : ℂ) + y * I)‖ ≤
      Real.sin (2 * π * s) / (Real.sinh (2 * π * |x|) - 1) := by
    rw [sinhRatioDensity, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hS]
    exact div_le_div_of_nonneg_left hS.le (by linarith) hden
  exact mul_le_mul hexp hmS (norm_nonneg _) (Real.exp_pos _).le

/-- The vertical edge integrals tend to zero. -/
theorem tendsto_vertical_fourierIntegrand {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ)
    (σ : ℝ) (hσ : |σ| = 1) :
    Tendsto (fun R : ℝ ↦ ∫ y in (0 : ℝ)..1, fourierIntegrand s z (((σ * R : ℝ) : ℂ) + y * I))
      atTop (𝓝 0) := by
  set C := Real.exp |z| * Real.sin (2 * π * s)
  have hlin : Tendsto (fun R : ℝ ↦ Real.sinh (2 * π * R) - 1) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-1)
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π)))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have := Real.self_le_sinh_iff.mpr (by positivity : (0 : ℝ) ≤ 2 * π * R)
    simp only [id]; linarith
  have hbound : Tendsto (fun R : ℝ ↦ C / (Real.sinh (2 * π * R) - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlin
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hlin.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℝ)] with R hR hR0
  have hx : |σ * R| = R := by rw [abs_mul, hσ, one_mul, abs_of_pos hR0]
  have hb : ∀ y ∈ Ι (0 : ℝ) 1, ‖fourierIntegrand s z (((σ * R : ℝ) : ℂ) + y * I)‖ ≤
      C / (Real.sinh (2 * π * R) - 1) := by
    intro y hy
    rw [uIoc_of_le zero_le_one] at hy
    have := norm_fourierIntegrand_vertical_le hs z hy.1.le hy.2 (by rw [hx]; linarith)
    rw [hx] at this
    calc _ ≤ _ := this
      _ = C / (Real.sinh (2 * π * R) - 1) := by simp only [C]; ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

/-- **The Fourier formula for the hyperbolic-sine ratio.** For `0 < s < 1/2` and real `z`,
`g_s(z) = ∫ e^{iuz} m_s(u) du`.

Area-law paper, Lemma 7.3 (`transport:fourier`), display `transport:g-fourier`,
`06-transport.tex` lines 194--199, proof lines 214--226. -/
theorem integral_exp_mul_sinhRatioDensity {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ) :
    ∫ u : ℝ, cexp (I * u * z) * (Real.sinhRatioDensity s u : ℂ) = (Real.sinhRatio s z : ℂ) := by
  have hf : ∀ u : ℝ, cexp (I * u * z) * (Real.sinhRatioDensity s u : ℂ) =
      fourierIntegrand s z u := by
    intro u
    rw [fourierIntegrand]
    congr 1
    simp only [sinhRatioDensity, Real.sinhRatioDensity]
    push_cast; rfl
  simp_rw [hf]
  rcases eq_or_ne z 0 with rfl | hz
  · have : ∀ u : ℝ, fourierIntegrand s 0 u = (Real.sinhRatioDensity s u : ℂ) := fun u ↦ by
      rw [← hf]; simp
    simp_rw [this]
    rw [show (∫ u : ℝ, ((Real.sinhRatioDensity s u : ℝ) : ℂ)) =
        ((∫ u : ℝ, Real.sinhRatioDensity s u : ℝ) : ℂ) from integral_ofReal,
      Real.integral_sinhRatioDensity hs, Real.sinhRatio_zero]
  · set F := ∫ u : ℝ, fourierIntegrand s z u
    set E := cexp (-((1 / 2 - s : ℝ) * z)) - cexp (-((1 / 2 + s : ℝ) * z))
    have hint := integrable_fourierIntegrand hs z
    have hΦ : Tendsto (fun R : ℝ ↦ ∫ x in (-R)..R, fourierIntegrand s z x) atTop (𝓝 F) :=
      intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
    have hV₁ := tendsto_vertical_fourierIntegrand hs z 1 (by simp)
    have hV₂ := tendsto_vertical_fourierIntegrand hs z (-1) (by simp)
    have hlim : Tendsto (fun R : ℝ ↦ (1 - cexp (-(z : ℂ))) * (∫ x in (-R)..R,
        fourierIntegrand s z x) + I * ((∫ y in (0 : ℝ)..1,
          fourierIntegrand s z (((1 * R : ℝ) : ℂ) + y * I)) - ∫ y in (0 : ℝ)..1,
          fourierIntegrand s z (((-1 * R : ℝ) : ℂ) + y * I))) atTop
        (𝓝 ((1 - cexp (-(z : ℂ))) * F + I * (0 - 0))) :=
      (hΦ.const_mul _).add ((hV₁.sub hV₂).const_mul I)
    have hconst : ∀ᶠ R : ℝ in atTop, (1 - cexp (-(z : ℂ))) * (∫ x in (-R)..R,
        fourierIntegrand s z x) + I * ((∫ y in (0 : ℝ)..1,
          fourierIntegrand s z (((1 * R : ℝ) : ℂ) + y * I)) - ∫ y in (0 : ℝ)..1,
          fourierIntegrand s z (((-1 * R : ℝ) : ℂ) + y * I)) = E := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      have h := rectBoundaryIntegral_fourierIntegrand hs z hR
      unfold rectBoundaryIntegral at h
      simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, I_re, add_zero, add_im,
        I_im, zero_add, ofReal_zero, zero_mul, smul_eq_mul, ofReal_neg, ofReal_one,
        one_mul] at h
      simp_rw [fourierIntegrand_add_I, intervalIntegral.integral_const_mul] at h
      rw [show E = _ from h.symm]
      simp only [one_mul, neg_mul, ofReal_neg]
      ring
    have hEq : (1 - cexp (-(z : ℂ))) * F = E := by
      have := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
      simpa using this
    have hne : 1 - cexp (-(z : ℂ)) ≠ 0 := by
      intro h
      have h1 : cexp (-(z : ℂ)) = 1 := by linear_combination -h
      rw [← ofReal_neg, ← ofReal_exp, ofReal_eq_one, Real.exp_eq_one_iff, neg_eq_zero] at h1
      exact hz h1
    have hrealR : Real.sinhRatio s z * (1 - Real.exp (-z)) =
        Real.exp (-((1 / 2 - s) * z)) - Real.exp (-((1 / 2 + s) * z)) := by
      rw [Real.sinhRatio_of_ne_zero s hz]
      have hsh : Real.sinh (z / 2) ≠ 0 := by
        rw [Ne, Real.sinh_eq_zero]; exact div_ne_zero hz two_ne_zero
      rw [div_mul_eq_mul_div, div_eq_iff hsh, Real.sinh_eq, Real.sinh_eq]
      rw [show -((1 / 2 - s) * z) = s * z + -(z / 2) by ring,
        show -((1 / 2 + s) * z) = -(s * z) + -(z / 2) by ring, Real.exp_add, Real.exp_add,
        show -z = -(z / 2) + -(z / 2) by ring, Real.exp_add, show -(s * z) = -(s * z) by rfl]
      have : Real.exp (z / 2) * Real.exp (-(z / 2)) = 1 := by rw [← Real.exp_add]; simp
      linear_combination (-(Real.exp (s * z) - Real.exp (-(s * z))) / 2) * this
    have hreal : (Real.sinhRatio s z : ℂ) * (1 - cexp (-(z : ℂ))) = E := by
      have := congrArg (fun x : ℝ ↦ (x : ℂ)) hrealR
      simp only [E]
      push_cast at this ⊢
      exact this
    calc F = E / (1 - cexp (-(z : ℂ))) := by rw [← hEq]; field_simp
      _ = (Real.sinhRatio s z : ℂ) := by rw [← hreal]; field_simp

end Complex
