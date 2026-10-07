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
noncomputable def fourierNumer (s z : ℝ) (w : ℂ) : ℂ := cexp (I * w * z) * Real.sin (2 * Real.pi * s)

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
    rw [deriv_densityDenom_pole₂]; exact neg_ne_zero.mpr (mul_ne_zero h2pi (mul_ne_zero hS I_ne_zero))
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
  simp only [c, if_pos rfl, if_neg (Ne.symm hne)]
  exact two_pi_I_mul_residues hs z

end Complex
