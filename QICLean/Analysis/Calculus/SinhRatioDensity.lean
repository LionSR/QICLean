/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The hyperbolic-sine ratio and its Fourier density

For `0 < s < 1/2` set
\[
  g_s(z) = \frac{\sinh(sz)}{\sinh(z/2)}, \qquad g_s(0) = 2s, \qquad
  m_s(u) = \frac{\sin(2\pi s)}{\cosh(2\pi u) + \cos(2\pi s)} .
\]
This file proves the elementary parts of the area-law Lemma 7.3: `g_s` is continuous
(the quotient is interpreted continuously at zero), `m_s` is positive, integrable, and
has total mass `2s`, the shifted ratios `h_±(z) = (e^{±sz} - 1) / (2 \sinh(z/2))` factor as
`± e^{± sz/2} g_{s/2}(z)`, and at `s = 1/4` the complex-shifted densities satisfy
`|m_{s/2}(u ± is/2)| ≤ m_s(u)/√2`.

The total mass is computed from the primitive
`u ↦ arctan((e^{2πu} + cos 2πs) / sin 2πs) / π`, whose limits at `-∞` and `+∞` are
`1/2 - 2s` and `1/2`.

## Main definitions

* `Real.sinhRatio s z` — `g_s(z)`, with the value `2s` at `z = 0`.
* `Real.sinhRatioDensity s u` — `m_s(u)`.
* `Complex.sinhRatioDensity s w` — the same formula at a complex argument.

## Main results

* `Real.continuous_sinhRatio` — `g_s` is continuous.
* `Real.sinhRatioDensity_pos`, `Real.integrable_sinhRatioDensity`,
  `Real.integral_sinhRatioDensity` — positivity, integrability and mass `2s`.
* `Real.exp_sub_one_div_two_sinh`, `Real.exp_neg_sub_one_div_two_sinh` — the
  factorization of `h_±` (display `transport:h-def`).
* `Complex.norm_sinhRatioDensity_shift_le` — `|m_{1/8}(u ± i/8)| ≤ m_{1/4}(u)/√2`
  (display `transport:q-density`, bound).

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.3 (`transport:fourier`), lines 183--244.
  The proofs are written independently from the paper.
-/

open Real Filter Topology MeasureTheory Set

namespace Real

/-- The hyperbolic-sine ratio `g_s(z) = sinh(s z) / sinh(z/2)`, interpreted continuously at
`z = 0` by its limit `2s`.

Area-law paper, display `transport:fourier-density`, `06-transport.tex` lines 184--188. -/
noncomputable def sinhRatio (s z : ℝ) : ℝ := if z = 0 then 2 * s else sinh (s * z) / sinh (z / 2)

/-- The Fourier density `m_s(u) = sin(2πs) / (cosh(2πu) + cos(2πs))`.

Area-law paper, display `transport:fourier-density`, `06-transport.tex` lines 184--188. -/
noncomputable def sinhRatioDensity (s u : ℝ) : ℝ :=
  sin (2 * π * s) / (cosh (2 * π * u) + cos (2 * π * s))

theorem sinhRatio_zero (s : ℝ) : sinhRatio s 0 = 2 * s := by simp [sinhRatio]

theorem sinhRatio_of_ne_zero (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    sinhRatio s z = sinh (s * z) / sinh (z / 2) := by simp [sinhRatio, hz]

/-- `sinh(c z) / z → c` as `z → 0`. -/
private theorem tendsto_sinh_mul_div (c : ℝ) :
    Tendsto (fun z : ℝ ↦ sinh (c * z) / z) (𝓝[≠] 0) (𝓝 c) := by
  have h : HasDerivAt (fun z : ℝ ↦ sinh (c * z)) c 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul c).sinh
    simpa using this
  have := h.tendsto_slope_zero
  simp only [zero_add, mul_zero, sinh_zero, sub_zero, smul_eq_mul] at this
  refine this.congr fun z ↦ ?_
  rw [inv_mul_eq_div]

/-- **Continuity of `g_s`**: the quotient `sinh(sz) / sinh(z/2)` extends continuously to
`z = 0` with value `2s`.

Area-law paper, `06-transport.tex` lines 187 and 210--211. -/
theorem continuous_sinhRatio (s : ℝ) : Continuous (sinhRatio s) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [continuousAt_iff_punctured_nhds, sinhRatio_zero]
    have hlim : Tendsto (fun z : ℝ ↦ (sinh (s * z) / z) / (sinh ((1 / 2) * z) / z))
        (𝓝[≠] 0) (𝓝 (s / (1 / 2))) :=
      (tendsto_sinh_mul_div s).div (tendsto_sinh_mul_div (1 / 2)) (by norm_num)
    rw [show s / (1 / 2) = 2 * s by ring] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [sinhRatio_of_ne_zero s hw, div_div_div_cancel_right₀ hw]
    ring_nf
  · have hev : sinhRatio s =ᶠ[𝓝 z] fun w ↦ sinh (s * w) / sinh (w / 2) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact sinhRatio_of_ne_zero s hw
    refine ContinuousAt.congr ?_ hev.symm
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    rw [Ne, sinh_eq_zero]
    exact div_ne_zero hz two_ne_zero

/-- **Positivity of the density** for `0 < s < 1/2`.

Area-law paper, display `transport:g-fourier`, `06-transport.tex` line 198. -/
theorem sinhRatioDensity_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (u : ℝ) :
    0 < sinhRatioDensity s u := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  refine div_pos (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) ?_
  have hc : -1 < cos (2 * π * s) := by
    rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
  linarith [one_le_cosh (2 * π * u)]

/-- The primitive `u ↦ arctan((e^{2πu} + cos 2πs) / sin 2πs) / π` of the density. -/
noncomputable def sinhRatioDensityPrimitive (s u : ℝ) : ℝ :=
  arctan ((exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s)) / π

/-- The derivative of the primitive is the density. -/
theorem hasDerivAt_sinhRatioDensityPrimitive {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) (u : ℝ) :
    HasDerivAt (sinhRatioDensityPrimitive s) (sinhRatioDensity s u) u := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : 0 < sin (2 * π * s) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hexp : HasDerivAt (fun u ↦ (exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s))
      (exp (2 * π * u) * (2 * π) / sin (2 * π * s)) u := by
    have := ((((hasDerivAt_id u).const_mul (2 * π)).exp).add_const
      (cos (2 * π * s))).div_const (sin (2 * π * s))
    simpa [mul_comm] using this
  refine (hexp.arctan.div_const π).congr_deriv ?_
  have hsc := sin_sq_add_cos_sq (2 * π * s)
  have hE : 0 < exp (2 * π * u) := exp_pos _
  have hpos := sinhRatioDensity_pos hs u
  rw [sinhRatioDensity] at hpos ⊢
  have hden : 0 < cosh (2 * π * u) + cos (2 * π * s) := by
    by_contra h; push Not at h
    exact absurd hpos (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hS.le h))
  rw [cosh_eq, exp_neg] at hden ⊢
  have hq : 0 < 1 + ((exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s)) ^ 2 := by positivity
  rw [div_eq_div_iff (by positivity) hden.ne']
  field_simp
  nlinarith [hsc, hE, sq_nonneg (exp (2 * π * u))]

/-- The density is even. -/
theorem sinhRatioDensity_neg (s u : ℝ) : sinhRatioDensity s (-u) = sinhRatioDensity s u := by
  simp [sinhRatioDensity, mul_neg, cosh_neg]

/-- The primitive tends to `1/2` at `+∞`. -/
theorem tendsto_sinhRatioDensityPrimitive_atTop {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (sinhRatioDensityPrimitive s) atTop (𝓝 (1 / 2)) := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have hS : 0 < sin (2 * π * s) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 : Tendsto (fun u : ℝ ↦ (exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s))
      atTop atTop := by
    refine Tendsto.atTop_div_const hS (tendsto_atTop_add_const_right _ _ ?_)
    exact tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have h2 := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp h1
  have h3 := h2.div_const π
  rw [show π / 2 / π = 1 / 2 by field_simp] at h3
  exact h3

/-- The primitive tends to `1/2 - 2s` at `-∞`. -/
theorem tendsto_sinhRatioDensityPrimitive_atBot {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (sinhRatioDensityPrimitive s) atBot (𝓝 (1 / 2 - 2 * s)) := by
  have hθ : 2 * π * s ∈ Ioo 0 π := ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩
  have h1 : Tendsto (fun u : ℝ ↦ (exp (2 * π * u) + cos (2 * π * s)) / sin (2 * π * s))
      atBot (𝓝 ((0 + cos (2 * π * s)) / sin (2 * π * s))) := by
    refine ((Tendsto.add ?_ tendsto_const_nhds).div_const _)
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by positivity))
  have h2 := ((continuous_arctan.tendsto _).comp h1).div_const π
  have harg : arctan ((0 + cos (2 * π * s)) / sin (2 * π * s)) = π / 2 - 2 * π * s := by
    rw [zero_add, ← inv_div, ← tan_eq_sin_div_cos, ← tan_pi_div_two_sub]
    exact arctan_tan (by linarith [hθ.2]) (by linarith [hθ.1])
  rw [harg, show (π / 2 - 2 * π * s) / π = 1 / 2 - 2 * s by field_simp] at h2
  exact h2

/-- **The density is integrable** for `0 < s < 1/2`. -/
theorem integrable_sinhRatioDensity {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Integrable (sinhRatioDensity s) := by
  have hIoi : ∀ a : ℝ, IntegrableOn (sinhRatioDensity s) (Ioi a) := fun a ↦
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ ↦ hasDerivAt_sinhRatioDensityPrimitive hs x)
      (fun x _ ↦ (sinhRatioDensity_pos hs x).le) (tendsto_sinhRatioDensityPrimitive_atTop hs)
  have hIio : IntegrableOn (sinhRatioDensity s) (Iio 0) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (measurableEmbedding_neg) (f := sinhRatioDensity s) (s := Ioi 0)
    have hcomp : sinhRatioDensity s ∘ Neg.neg = sinhRatioDensity s := by
      ext u; exact sinhRatioDensity_neg s u
    rw [hcomp, Set.neg_preimage, Set.neg_Ioi, neg_zero] at h
    exact h.mpr (hIoi 0)
  rw [← integrableOn_univ, show (univ : Set ℝ) = Iio 0 ∪ Ioi (-1) by
    ext x; simp only [mem_univ, mem_union, mem_Iio, mem_Ioi, true_iff]; by_contra h
    push Not at h; linarith [h.1, h.2]]
  exact hIio.union (hIoi (-1))

/-- **The total mass of the density is `2s`** for `0 < s < 1/2`.

Area-law paper, display `transport:g-fourier`, `06-transport.tex` line 198. -/
theorem integral_sinhRatioDensity {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    ∫ u, sinhRatioDensity s u = 2 * s := by
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_sinhRatioDensityPrimitive hs)
    (integrable_sinhRatioDensity hs) (tendsto_sinhRatioDensityPrimitive_atBot hs)
    (tendsto_sinhRatioDensityPrimitive_atTop hs)]
  ring

/-- **The shifted ratio `h_+`**: `(e^{sz} - 1) / (2 sinh(z/2)) = e^{sz/2} g_{s/2}(z)` for
`z ≠ 0`.

Area-law paper, display `transport:h-def`, `06-transport.tex` lines 201--204. -/
theorem exp_sub_one_div_two_sinh (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    (exp (s * z) - 1) / (2 * sinh (z / 2)) = exp (s * z / 2) * sinhRatio (s / 2) z := by
  rw [sinhRatio_of_ne_zero _ hz, sinh_eq, sinh_eq]
  have h1 : exp (s * z) = exp (s * z / 2) * exp (s * z / 2) := by
    rw [← exp_add]; ring_nf
  have h2 : exp (-(s / 2 * z)) = (exp (s * z / 2))⁻¹ := by rw [← exp_neg]; ring_nf
  have hne : sinh (z / 2) ≠ 0 := by rw [Ne, sinh_eq_zero]; exact div_ne_zero hz two_ne_zero
  rw [sinh_eq] at hne
  have hE : exp (s * z / 2) ≠ 0 := exp_ne_zero _
  rw [h1, h2, show s / 2 * z = s * z / 2 by ring]
  field_simp

/-- **The shifted ratio `h_-`**: `(e^{-sz} - 1) / (2 sinh(z/2)) = -e^{-sz/2} g_{s/2}(z)` for
`z ≠ 0`.

Area-law paper, display `transport:h-def`, `06-transport.tex` lines 201--204. -/
theorem exp_neg_sub_one_div_two_sinh (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    (exp (-(s * z)) - 1) / (2 * sinh (z / 2)) = -(exp (-(s * z) / 2) * sinhRatio (s / 2) z) := by
  have h := exp_sub_one_div_two_sinh (-s) hz
  rw [show -s * z = -(s * z) by ring] at h
  rw [h, sinhRatio_of_ne_zero _ hz, sinhRatio_of_ne_zero _ hz,
    show -s / 2 * z = -(s / 2 * z) by ring, sinh_neg]
  ring_nf

end Real

namespace Complex

/-- The Fourier density at a complex argument,
`m_s(w) = sin(2πs) / (cosh(2πw) + cos(2πs))`. -/
noncomputable def sinhRatioDensity (s : ℝ) (w : ℂ) : ℂ :=
  Real.sin (2 * Real.pi * s) / (cosh (2 * Real.pi * w) + Real.cos (2 * Real.pi * s))

/-- **The shifted-density bound at `s = 1/4`**: for real `u` and `σ = ±1`,
`|m_{1/8}(u + σ i/8)| ≤ m_{1/4}(u) / √2`.

Area-law paper, display `transport:q-density` and lines 233--242. -/
theorem norm_sinhRatioDensity_shift_le (u : ℝ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖sinhRatioDensity (1 / 8) (u + σ * I / 8)‖ ≤ Real.sinhRatioDensity (1 / 4) u / √2 := by
  set c := Real.cosh (2 * Real.pi * u)
  set sh := Real.sinh (2 * Real.pi * u)
  have hc : 1 ≤ c := Real.one_le_cosh _
  have hcs : sh ^ 2 = c ^ 2 - 1 := by
    have := Real.cosh_sq (2 * Real.pi * u); simp only [c, sh]; linarith
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hcosσ : Real.cos (σ * (Real.pi / 4)) = √2 / 2 := by
    rcases hσ with rfl | rfl <;> simp [Real.cos_pi_div_four]
  have hsinσ : Real.sin (σ * (Real.pi / 4)) = σ * (√2 / 2) := by
    rcases hσ with rfl | rfl <;> simp [Real.sin_pi_div_four]
  have harg : (2 * (Real.pi : ℂ) * (u + σ * I / 8)) =
      ((2 * Real.pi * u : ℝ) : ℂ) + ((σ * (Real.pi / 4) : ℝ) : ℂ) * I := by
    push_cast; ring
  have hval : sinhRatioDensity (1 / 8) (u + σ * I / 8) =
      1 / (((c + 1 : ℝ) : ℂ) + ((σ * sh : ℝ) : ℂ) * I) := by
    rw [sinhRatioDensity, harg, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      hcosσ, hsinσ, show 2 * Real.pi * (1 / 8 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
    simp only [c, sh]
    push_cast
    field_simp
    ring
  have hm : Real.sinhRatioDensity (1 / 4) u = 1 / c := by
    rw [Real.sinhRatioDensity, show 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 by ring,
      Real.sin_pi_div_two, Real.cos_pi_div_two, add_zero]
  rw [hval, hm, norm_div, norm_one, Complex.norm_add_mul_I]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  rw [show c * √2 = √(2 * c ^ 2) by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith), mul_comm]]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, hσ2, hcs]
  nlinarith

end Complex
