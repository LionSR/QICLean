/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SinhRatioFourier

/-!
# Shifted Fourier densities of the hyperbolic-sine ratio

For `0 < s < 1/2` the density `m_{s/2}` has no poles in the closed strip
`|Im w| ≤ s/2`; there `|cosh(2πw) + cos(πs)| ≥ cos(πs) cosh(2π Re w)`. Shifting the
Fourier contour of `m_{s/2}` by `±is/2` therefore crosses no pole, and the functions
\[
  h_\pm(z) = \frac{e^{\pm sz} - 1}{2\sinh(z/2)} = \pm e^{\pm sz/2} g_{s/2}(z)
\]
have the Fourier densities `q_±(u) = ± m_{s/2}(u ± is/2)`.

## Main results

* `Complex.integral_exp_mul_sinhRatioDensity_shift` — for `|σ| ≤ s/2`,
  `∫ e^{iuz} m_{s/2}(u + iσ) du = e^{σz} g_{s/2}(z)`.
* `Complex.integral_exp_mul_qPlus`, `Complex.integral_exp_mul_qMinus` — the Fourier
  densities of `h_+` and `h_-` (display `transport:q-density`).

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.3 (`transport:fourier`), lines 200--211 and
  228--232. The proofs are written independently from the paper.
-/

open Real Filter Topology MeasureTheory Set
open scoped Interval

namespace Complex

variable {s : ℝ}

/-- **No poles in the strip `|Im w| ≤ s/2`**: there
`cos(πs) cosh(2π Re w) ≤ |cosh(2πw) + cos(πs)|`. -/
theorem cos_mul_cosh_le_norm_densityDenom (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {w : ℂ}
    (hw : |w.im| ≤ s / 2) :
    Real.cos (π * s) * Real.cosh (2 * π * w.re) ≤ ‖densityDenom (s / 2) w‖ := by
  have hcpos : 0 < Real.cos (π * s) := Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hw' : (2 * (Real.pi : ℂ) * w) = ((2 * π * w.re : ℝ) : ℂ) + ((2 * π * w.im : ℝ) : ℂ) * I := by
    conv_lhs => rw [← re_add_im w]
    push_cast; ring
  have hcosb : Real.cos (π * s) ≤ Real.cos (2 * π * w.im) := by
    rw [← Real.cos_abs (2 * π * w.im), abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos, hs.2]) ?_
    nlinarith [pi_pos]
  have hre : (densityDenom (s / 2) w).re =
      Real.cosh (2 * π * w.re) * Real.cos (2 * π * w.im) + Real.cos (π * s) := by
    rw [densityDenom, hw', cosh_ofReal_add_ofReal_mul_I]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero]
    ring_nf
  calc Real.cos (π * s) * Real.cosh (2 * π * w.re)
      ≤ Real.cosh (2 * π * w.re) * Real.cos (2 * π * w.im) + Real.cos (π * s) := by
        nlinarith [Real.one_le_cosh (2 * π * w.re)]
    _ = (densityDenom (s / 2) w).re := hre.symm
    _ ≤ ‖densityDenom (s / 2) w‖ := re_le_norm _

/-- The density `m_{s/2}` is bounded in the strip `|Im w| ≤ s/2`. -/
theorem norm_sinhRatioDensity_half_le (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {w : ℂ}
    (hw : |w.im| ≤ s / 2) :
    ‖sinhRatioDensity (s / 2) w‖ ≤
      Real.sin (π * s) / Real.cos (π * s) * Real.sinhRatioDensity (1 / 4) w.re := by
  have hcpos : 0 < Real.cos (π * s) := Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hspos : 0 < Real.sin (π * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hs.1]) (by nlinarith [pi_pos, hs.2])
  have hm : Real.sinhRatioDensity (1 / 4) w.re = (Real.cosh (2 * π * w.re))⁻¹ := by
    rw [Real.sinhRatioDensity, show 2 * π * (1 / 4 : ℝ) = π / 2 by ring, Real.sin_pi_div_two,
      Real.cos_pi_div_two, add_zero, one_div]
  have hb := cos_mul_cosh_le_norm_densityDenom hs hw
  have hch : 0 < Real.cosh (2 * π * w.re) := Real.cosh_pos _
  rw [hm, show sinhRatioDensity (s / 2) w = (Real.sin (π * s) : ℂ) / densityDenom (s / 2) w by
    rw [sinhRatioDensity, densityDenom, show 2 * π * (s / 2) = π * s by ring], norm_div,
    norm_real, Real.norm_eq_abs, abs_of_pos hspos]
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hb)]
  calc Real.sin (π * s) = Real.sin (π * s) / Real.cos (π * s) * (Real.cosh (2 * π * w.re))⁻¹ *
        (Real.cos (π * s) * Real.cosh (2 * π * w.re)) := by field_simp
    _ ≤ _ := by gcongr

/-- The bound for the integrand `e^{iwz} m_{s/2}(w)` in the strip `|Im w| ≤ s/2`. -/
theorem norm_fourierIntegrand_half_le (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ) {w : ℂ}
    (hw : |w.im| ≤ s / 2) :
    ‖fourierIntegrand (s / 2) z w‖ ≤ Real.exp |z| *
      (Real.sin (π * s) / Real.cos (π * s) * Real.sinhRatioDensity (1 / 4) w.re) := by
  rw [fourierIntegrand, norm_mul]
  refine mul_le_mul ?_ (norm_sinhRatioDensity_half_le hs hw) (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  have : (I * w * z).re = -(w.im * z) := by simp
  rw [this]
  have h1 : |w.im * z| ≤ |z| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg z) (by linarith [hs.2])
  linarith [neg_abs_le (w.im * z)]

/-- The denominator does not vanish in the strip `|Im w| ≤ s/2`. -/
theorem densityDenom_half_ne_zero (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {w : ℂ}
    (hw : |w.im| ≤ s / 2) : densityDenom (s / 2) w ≠ 0 := by
  have hcpos : 0 < Real.cos (π * s) := Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  intro h
  have := cos_mul_cosh_le_norm_densityDenom hs hw
  rw [h, norm_zero] at this
  nlinarith [Real.cosh_pos (2 * π * w.re)]

/-- **Contour shift without poles.** For `|σ| ≤ s/2` and real `z`,
`∫ e^{iuz} m_{s/2}(u + iσ) du = e^{σz} g_{s/2}(z)`.

Area-law paper, proof of Lemma 7.3 (`transport:fourier`), `06-transport.tex`
lines 229--232: the nearest poles of `m_{s/2}` have imaginary parts of absolute value
`1/2 - s/2 > s/2`. -/
theorem integral_exp_mul_sinhRatioDensity_shift (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ)
    {σ : ℝ} (hσ : |σ| ≤ s / 2) :
    ∫ u : ℝ, cexp (I * u * z) * sinhRatioDensity (s / 2) (u + σ * I) =
      cexp (σ * z) * (Real.sinhRatio (s / 2) z : ℂ) := by
  have hs2 : s / 2 ∈ Ioo (0 : ℝ) (1 / 2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set f := fourierIntegrand (s / 2) z
  set K := Real.exp |z| * (Real.sin (π * s) / Real.cos (π * s))
  have hstrip : ∀ x y : ℝ, |y| ≤ |σ| → |((x : ℂ) + y * I).im| ≤ s / 2 := fun x y hy ↦ by
    simpa using hy.trans hσ
  have hbound : ∀ x y : ℝ, |y| ≤ |σ| →
      ‖f ((x : ℂ) + y * I)‖ ≤ K * Real.sinhRatioDensity (1 / 4) x := fun x y hy ↦ by
    have := norm_fourierIntegrand_half_le hs z (hstrip x y hy)
    simpa [K, mul_assoc] using this
  have hdiff : Differentiable ℂ (fun w ↦ fourierNumer (s / 2) z w) :=
    differentiable_fourierNumer _ _
  have hfdiv : f = fun w ↦ fourierNumer (s / 2) z w / densityDenom (s / 2) w :=
    funext (fourierIntegrand_eq_div (s / 2) z)
  -- Integrability of the shifted integrand.
  have hint₀ : Integrable fun x : ℝ ↦ f ((x : ℂ) + σ * I) := by
    have hcont : Continuous fun x : ℝ ↦ f ((x : ℂ) + σ * I) := by
      rw [hfdiv]
      refine Continuous.div (hdiff.continuous.comp (by fun_prop))
        ((differentiable_densityDenom _).continuous.comp (by fun_prop)) fun x ↦ ?_
      exact densityDenom_half_ne_zero hs (hstrip x σ le_rfl)
    refine ((Real.integrable_sinhRatioDensity (by norm_num : (1 / 4 : ℝ) ∈ Ioo 0 (1 / 2))).const_mul
      K).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun x ↦ hbound x σ le_rfl)
  have hint : Integrable fun x : ℝ ↦ f x := integrable_fourierIntegrand hs2 z
  -- The vertical edges tend to zero.
  have hvert : ∀ τ : ℝ, |τ| = 1 → Tendsto (fun R : ℝ ↦
      ∫ y in (0 : ℝ)..σ, f (((τ * R : ℝ) : ℂ) + y * I)) atTop (𝓝 0) := by
    intro τ hτ
    have hdecay : Tendsto (fun R : ℝ ↦ K * Real.sinhRatioDensity (1 / 4) (τ * R) * |σ - 0|)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ ↦ Real.cosh (2 * π * (τ * R))) atTop atTop := by
        refine tendsto_atTop_mono (fun R ↦ ?_) (tendsto_atTop_add_const_right _ 0
          ((tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π))))
        simp only [id, add_zero]
        have h2π : (0 : ℝ) < 2 * π := by positivity
        have hc : Real.cosh (2 * π * (τ * R)) = Real.cosh (2 * π * |R|) := by
          rw [← Real.cosh_abs, abs_mul, abs_of_pos h2π, abs_mul, hτ, one_mul]
        rw [hc]
        have := Real.self_le_sinh_iff.mpr (by positivity : (0 : ℝ) ≤ 2 * π * |R|)
        nlinarith [Real.sinh_lt_cosh (2 * π * |R|), le_abs_self R]
      have h2 : Tendsto (fun R : ℝ ↦ Real.sinhRatioDensity (1 / 4) (τ * R)) atTop (𝓝 0) := by
        have : (fun R : ℝ ↦ Real.sinhRatioDensity (1 / 4) (τ * R)) =
            fun R ↦ (Real.cosh (2 * π * (τ * R)))⁻¹ := by
          ext R
          rw [Real.sinhRatioDensity, show 2 * π * (1 / 4 : ℝ) = π / 2 by ring,
            Real.sin_pi_div_two, Real.cos_pi_div_two, add_zero, one_div]
        rw [this]; exact h1.inv_tendsto_atTop
      simpa using (h2.const_mul K).mul_const |σ - 0|
    refine squeeze_zero_norm (fun R ↦ ?_) hdecay
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ ?_
    refine hbound _ y ?_
    rcases le_total 0 σ with h | h
    · rw [uIoc_of_le h] at hy
      rw [abs_of_nonneg h, abs_of_nonneg hy.1.le]; exact hy.2
    · rw [uIoc_of_ge h] at hy
      rw [abs_of_nonpos h, abs_of_nonpos hy.2]; linarith [hy.1]
  -- Cauchy--Goursat on the rectangles.
  have hrect : ∀ R : ℝ, (∫ x in (-R)..R, f x) - (∫ x in (-R)..R, f ((x : ℂ) + σ * I)) +
      I * ((∫ y in (0 : ℝ)..σ, f (((1 * R : ℝ) : ℂ) + y * I)) -
        ∫ y in (0 : ℝ)..σ, f (((-1 * R : ℝ) : ℂ) + y * I)) = 0 := by
    intro R
    have hd : DifferentiableOn ℂ f ([[(-(R : ℂ)).re, ((R : ℂ) + σ * I).re]] ×ℂ
        [[(-(R : ℂ)).im, ((R : ℂ) + σ * I).im]]) := by
      intro w hw
      simp only [mem_reProdIm, neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, mul_re,
        I_re, mul_zero, I_im, mul_one, sub_zero, add_im, mul_im, zero_add, add_zero] at hw
      have hwim : |w.im| ≤ s / 2 := by
        refine le_trans ?_ hσ
        rcases le_total 0 σ with h | h
        · rw [uIcc_of_le h] at hw
          rw [abs_of_nonneg hw.2.1, abs_of_nonneg h]; exact hw.2.2
        · rw [uIcc_of_ge h] at hw
          rw [abs_of_nonpos hw.2.2, abs_of_nonpos h]; linarith [hw.2.1]
      rw [hfdiv]
      exact ((hdiff w).div (differentiable_densityDenom _ w)
        (densityDenom_half_ne_zero hs hwim)).differentiableWithinAt
    have h := integral_boundary_rect_eq_zero_of_differentiableOn f (-(R : ℂ)) (R + σ * I) hd
    simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, add_re, mul_re, I_re, mul_zero,
      I_im, mul_one, sub_zero, add_im, mul_im, zero_add, add_zero, ofReal_zero, zero_mul,
      smul_eq_mul, ofReal_neg] at h
    rw [← h]
    simp only [one_mul, neg_mul, ofReal_neg]
    ring
  have hlim : Tendsto (fun R : ℝ ↦ (∫ x in (-R)..R, f x) -
      (∫ x in (-R)..R, f ((x : ℂ) + σ * I)) +
      I * ((∫ y in (0 : ℝ)..σ, f (((1 * R : ℝ) : ℂ) + y * I)) -
        ∫ y in (0 : ℝ)..σ, f (((-1 * R : ℝ) : ℂ) + y * I))) atTop
      (𝓝 ((∫ x : ℝ, f x) - (∫ x : ℝ, f ((x : ℂ) + σ * I)) + I * (0 - 0))) :=
    ((intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hint₀ tendsto_neg_atTop_atBot tendsto_id)).add
      (((hvert 1 (by simp)).sub (hvert (-1) (by simp))).const_mul I)
  have hEq : (∫ x : ℝ, f ((x : ℂ) + σ * I)) = ∫ x : ℝ, f x := by
    have := tendsto_nhds_unique (hlim.congr (fun R ↦ hrect R)) tendsto_const_nhds
    linear_combination -this
  have hf₀ : (∫ x : ℝ, f x) = (Real.sinhRatio (s / 2) z : ℂ) := by
    rw [← integral_exp_mul_sinhRatioDensity hs2 z]
    refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    simp only [f, fourierIntegrand, sinhRatioDensity, Real.sinhRatioDensity]
    push_cast; rfl
  have hshift : ∀ u : ℝ, cexp (I * u * z) * sinhRatioDensity (s / 2) (u + σ * I) =
      cexp (σ * z) * f ((u : ℂ) + σ * I) := by
    intro u
    simp only [f, fourierIntegrand]
    have : I * ((u : ℂ) + σ * I) * z = I * u * z + -(σ * z) := by ring_nf; rw [I_sq]; ring
    rw [this, Complex.exp_add, ← mul_assoc, ← mul_assoc, mul_comm (cexp ((σ : ℂ) * z)),
      mul_assoc (cexp (I * u * z)), ← Complex.exp_add]
    simp
  simp_rw [hshift]
  rw [integral_const_mul, hEq, hf₀]

/-- **The Fourier density of `h_+`.** For real `z`,
`∫ e^{iuz} q_+(u) du = e^{sz/2} g_{s/2}(z)` with `q_+(u) = m_{s/2}(u + is/2)`; for `z ≠ 0` this
is `h_+(z) = (e^{sz} - 1) / (2 sinh(z/2))`.

Area-law paper, Lemma 7.3 (`transport:fourier`), displays `transport:h-def` and
`transport:q-density`, `06-transport.tex` lines 200--211, stated there for `s = 1/4`. -/
theorem integral_exp_mul_qPlus (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ) :
    ∫ u : ℝ, cexp (I * u * z) * sinhRatioDensity (s / 2) (u + (s / 2 : ℝ) * I) =
      ((Real.exp (s * z / 2) * Real.sinhRatio (s / 2) z : ℝ) : ℂ) := by
  rw [integral_exp_mul_sinhRatioDensity_shift hs z (by rw [abs_of_pos (by linarith [hs.1])])]
  push_cast
  ring_nf

/-- **The Fourier density of `h_-`.** For real `z`,
`∫ e^{iuz} q_-(u) du = -e^{-sz/2} g_{s/2}(z)` with `q_-(u) = -m_{s/2}(u - is/2)`; for `z ≠ 0`
this is `h_-(z) = (e^{-sz} - 1) / (2 sinh(z/2))`.

Area-law paper, Lemma 7.3 (`transport:fourier`), displays `transport:h-def` and
`transport:q-density`, `06-transport.tex` lines 200--211, stated there for `s = 1/4`. -/
theorem integral_exp_mul_qMinus (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (z : ℝ) :
    ∫ u : ℝ, cexp (I * u * z) * -sinhRatioDensity (s / 2) (u + (-(s / 2) : ℝ) * I) =
      ((-(Real.exp (-(s * z) / 2) * Real.sinhRatio (s / 2) z) : ℝ) : ℂ) := by
  simp_rw [mul_neg]
  rw [integral_neg, integral_exp_mul_sinhRatioDensity_shift hs z
    (by rw [abs_neg, abs_of_pos (by linarith [hs.1])])]
  push_cast
  ring_nf

/-- For `z ≠ 0` the Fourier density `q_+` represents `h_+(z) = (e^{sz} - 1)/(2 sinh(z/2))`. -/
theorem integral_exp_mul_qPlus_of_ne_zero (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {z : ℝ} (hz : z ≠ 0) :
    ∫ u : ℝ, cexp (I * u * z) * sinhRatioDensity (s / 2) (u + (s / 2 : ℝ) * I) =
      (((Real.exp (s * z) - 1) / (2 * Real.sinh (z / 2)) : ℝ) : ℂ) := by
  rw [integral_exp_mul_qPlus hs z, Real.exp_sub_one_div_two_sinh s hz]

/-- For `z ≠ 0` the Fourier density `q_-` represents `h_-(z) = (e^{-sz} - 1)/(2 sinh(z/2))`. -/
theorem integral_exp_mul_qMinus_of_ne_zero (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) {z : ℝ}
    (hz : z ≠ 0) :
    ∫ u : ℝ, cexp (I * u * z) * -sinhRatioDensity (s / 2) (u + (-(s / 2) : ℝ) * I) =
      (((Real.exp (-(s * z)) - 1) / (2 * Real.sinh (z / 2)) : ℝ) : ℂ) := by
  rw [integral_exp_mul_qMinus hs z, Real.exp_neg_sub_one_div_two_sinh s hz]

end Complex
