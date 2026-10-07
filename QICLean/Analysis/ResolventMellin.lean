/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The resolvent integral of a complex power

For `λ > 0` and `-1 < Re z < 0`,
$$\int_0^\infty\frac{v^z}{\lambda+v}\,dv=-\frac{\pi}{\sin\pi z}\,\lambda^z.$$
The substitution `v = λ t / (1 - t)` turns the integral into the Beta integral
`B(z + 1, -z) = Γ(z + 1) Γ(-z)`, and Euler's reflection formula evaluates it.

## Main results

* `integral_cpow_div_add` — the resolvent integral of `v ^ z`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 410–415 (the integral representation
  `A^z a₀ - V B^z b₀ = -(sin π z / π) ∫ v^z δ_v dv`).
-/

open MeasureTheory Set Filter Topology
open scoped Real

/-- The scalar resolvent difference `1 / (λ + v) - 1 / (1 + v)` is integrable on
`(0, ∞)` with integral `-log λ`. -/
theorem integral_inv_add_sub_inv_one_add {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun v : ℝ => (l + v)⁻¹ - (1 + v)⁻¹) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), ((l + v)⁻¹ - (1 + v)⁻¹) = -Real.log l := by
  set F : ℝ → ℝ := fun v => Real.log (l + v) - Real.log (1 + v)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F ((l + x)⁻¹ - (1 + x)⁻¹) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h1 := ((hasDerivAt_id x).const_add l).log (by simp; linarith)
    have h2 := ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
    have h := h1.sub h2
    convert h using 1
    · rfl
    · simp [one_div]
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact (continuousAt_const.add continuousAt_id).log (by simp; linarith)
    · exact (continuousAt_const.add continuousAt_id).log (by simp)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun v : ℝ => (l + v) / (1 + v)) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := l - 1)).div_atTop
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_add 1
      simp only [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with v hv
      simp only [id]
      field_simp
      ring
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with v hv
    simp only [Function.comp, F]
    rw [Real.log_div (by linarith) (by linarith)]
  have hF0 : F 0 = Real.log l := by simp [F]
  have hint : IntegrableOn (fun v : ℝ => (l + v)⁻¹ - (1 + v)⁻¹) (Ioi 0) := by
    rcases le_total l 1 with h | h
    · refine integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun x hx => ?_) hlim
      have hx' : (0 : ℝ) < x := hx
      exact sub_nonneg.2 (inv_anti₀ (by linarith : 0 < l + x) (by linarith : l + x ≤ 1 + x))
    · refine integrableOn_Ioi_deriv_of_nonpos hcont hderiv (fun x hx => ?_) hlim
      have hx' : (0 : ℝ) < x := hx
      exact sub_nonpos.2 (inv_anti₀ (by linarith : 0 < 1 + x) (by linarith : 1 + x ≤ l + x))
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim, hF0, zero_sub]

namespace Complex

/-- The image of `(0, 1)` under `t ↦ λ t / (1 - t)` is `(0, ∞)`. -/
theorem image_mul_div_one_sub_Ioo {l : ℝ} (hl : 0 < l) :
    (fun t : ℝ => l * t / (1 - t)) '' Ioo 0 1 = Ioi 0 := by
  ext v
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact div_pos (mul_pos hl ht0) (by linarith)
  · intro hv
    refine ⟨v / (l + v), ⟨div_pos hv (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩, ?_⟩
    have h : l + v ≠ 0 := by positivity
    have hl' : l ≠ 0 := hl.ne'
    have h1 : 1 - v / (l + v) = l / (l + v) := by field_simp; ring
    rw [h1, mul_div_assoc, div_div_div_cancel_right₀ h, mul_div_cancel₀ _ hl']

/-- **Resolvent integral of a complex power.** For `λ > 0` and `-1 < Re z < 0`,
`∫₀^∞ v^z / (λ + v) dv = -(π / sin (π z)) λ^z`.  Area-law manuscript, proof of
Lemma 5.2, `04-conditional.tex`, lines 410–415. -/
theorem integral_cpow_div_add {l : ℝ} (hl : 0 < l) {z : ℂ} (h1 : -1 < z.re) (h0 : z.re < 0) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ z / ((l : ℂ) + v) =
      -(π / sin (π * z)) * (l : ℂ) ^ z := by
  set f : ℝ → ℝ := fun t => l * t / (1 - t)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt f (l / (1 - t) ^ 2) (Ioo 0 1) t := by
    intro t ht
    have h1t : (1 - t) ≠ 0 := by linarith [ht.2]
    have := ((hasDerivAt_id t).const_mul l).div ((hasDerivAt_id t).const_sub 1) h1t
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id]
    field_simp
    ring
  have hinj : InjOn f (Ioo 0 1) := by
    intro s hs t ht hst
    have h1s : (1 - s) ≠ 0 := by linarith [hs.2]
    have h1t : (1 - t) ≠ 0 := by linarith [ht.2]
    simp only [f] at hst
    field_simp at hst
    nlinarith [hl]
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun v : ℝ => (v : ℂ) ^ z / ((l : ℂ) + v))
  rw [image_mul_div_one_sub_Ioo hl] at hsub
  rw [hsub]
  -- the transformed integrand is `λ^z t^z (1 - t)^(-z - 1)`
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1,
      |l / (1 - t) ^ 2| • ((f t : ℂ) ^ z / ((l : ℂ) + (f t : ℂ))) =
        (l : ℂ) ^ z * ((t : ℂ) ^ (z + 1 - 1) * (1 - (t : ℂ)) ^ (-z - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 - t := by linarith [ht.2]
    rw [abs_of_pos (by positivity), Complex.real_smul]
    have hft : (f t : ℂ) = (l : ℂ) * t * ((1 - t : ℝ) : ℂ)⁻¹ := by
      simp only [f]; push_cast; ring
    have hcpow : (f t : ℂ) ^ z = (l : ℂ) ^ z * (t : ℂ) ^ z * ((1 - t : ℝ) : ℂ) ^ (-z) := by
      rw [show f t = (l * t) * (1 - t)⁻¹ by simp only [f]; ring]
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hl.le ht0.le, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by
          rw [Complex.arg_ofReal_of_nonneg h1t.le]; exact Real.pi_pos.ne),
        ← Complex.cpow_neg]
    have hden : (l : ℂ) + (f t : ℂ) = (l : ℂ) * ((1 - t : ℝ) : ℂ)⁻¹ := by
      rw [hft]
      have : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1t.ne'
      field_simp
      push_cast
      ring
    have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have h1tC : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1t.ne'
    rw [hcpow, hden, show z + 1 - 1 = z by ring,
      show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_sub _ _ h1tC, Complex.cpow_one]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hint, integral_const_mul]
  -- identify the Beta integral
  have hbeta : ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (z + 1 - 1) * (1 - (t : ℂ)) ^ (-z - 1) =
      betaIntegral (z + 1) (-z) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hre1 : 0 < (z + 1).re := by simp; linarith
  have hre2 : 0 < (-z).re := by simp; linarith
  have hgamma := Gamma_mul_Gamma_eq_betaIntegral hre1 hre2
  rw [show z + 1 + -z = 1 by ring, Gamma_one, one_mul] at hgamma
  have hrefl := Gamma_mul_Gamma_one_sub (-z)
  rw [show 1 - -z = z + 1 by ring, mul_comm] at hrefl
  rw [hbeta, ← hgamma, hrefl, show (π : ℂ) * -z = -(π * z) by ring, Complex.sin_neg]
  ring

/-- `sin (π z) ≠ 0` when `z` is not an integer, in particular when `-1 < Re z < 0`. -/
theorem sin_pi_mul_ne_zero_of_re {z : ℂ} (h1 : -1 < z.re) (h0 : z.re < 0) :
    sin (π * z) ≠ 0 := by
  rw [Ne, sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hz : z = k := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    apply mul_left_cancel₀ hπ
    rw [hk]; ring
  have h1' := h1; have h0' := h0
  rw [hz] at h1' h0'
  simp only [intCast_re] at h1' h0'
  have : (k : ℝ) < 0 := h0'
  have : (-1 : ℝ) < k := h1'
  have hk0 : k < 0 := by exact_mod_cast ‹(k : ℝ) < 0›
  have hk1 : -1 < k := by exact_mod_cast ‹(-1 : ℝ) < k›
  omega

/-- `v ^ z / (λ + v)` is integrable on `(0, ∞)` for `λ > 0` and `-1 < Re z < 0`. -/
theorem integrableOn_cpow_div_add {l : ℝ} (hl : 0 < l) {z : ℂ} (h1 : -1 < z.re)
    (h0 : z.re < 0) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ z / ((l : ℂ) + v)) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_cpow_div_add hl h1 h0]
  refine mul_ne_zero (neg_ne_zero.2 (div_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
    (sin_pi_mul_ne_zero_of_re h1 h0))) ?_
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => (ofReal_ne_zero.2 hl.ne') h.1

/-- The difference `1 / (λ + v) - 1 / (1 + v)` written as a complex number. -/
theorem ofReal_inv_add_sub_inv_one_add (l v : ℝ) :
    (((l + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) = ((l : ℂ) + v)⁻¹ - (1 + (v : ℂ))⁻¹ := by
  push_cast; ring

/-- For `-1 < Re z < 0`, `∫₀^∞ v^z (1 / (λ + v) - 1 / (1 + v)) dv = -(π / sin π z) (λ^z - 1)`. -/
theorem integral_cpow_mul_inv_sub {l : ℝ} (hl : 0 < l) {z : ℂ} (h1 : -1 < z.re)
    (h0 : z.re < 0) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ z * (((l + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) =
      -(π / sin (π * z)) * ((l : ℂ) ^ z - 1) := by
  have hA := integrableOn_cpow_div_add hl h1 h0
  have hB := integrableOn_cpow_div_add one_pos h1 h0
  simp only [ofReal_one] at hB
  have e : ∀ v : ℝ, (v : ℂ) ^ z * (((l + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) =
      (v : ℂ) ^ z / ((l : ℂ) + v) - (v : ℂ) ^ z / (1 + (v : ℂ)) := by
    intro v; rw [ofReal_inv_add_sub_inv_one_add]; ring
  simp only [e]
  rw [integral_sub hA hB, integral_cpow_div_add hl h1 h0]
  have := integral_cpow_div_add one_pos h1 h0
  simp only [ofReal_one, one_cpow, mul_one] at this
  rw [this]
  ring

/-- `|1 / (λ + v) - 1 / (1 + v)|` is integrable on `(0, ∞)`, also after multiplication by
`v ^ (-1/2)`. -/
theorem integrableOn_rpow_mul_abs_inv_sub {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun v : ℝ => v ^ (-(1 / 2 : ℝ)) * |(l + v)⁻¹ - (1 + v)⁻¹|) (Ioi 0) := by
  have hB := integrableOn_cpow_div_add one_pos (z := -(1 / 2 : ℂ)) (by norm_num) (by norm_num)
  have hB' := hB.norm.const_mul (|1 - l| / l)
  refine hB'.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro v hv
    have hv' : (0 : ℝ) < v := hv
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (Real.continuousAt_rpow_const _ _ (Or.inl hv'.ne')) ?_
    refine ContinuousAt.abs (ContinuousAt.sub ?_ ?_)
    · exact (continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by dsimp; linarith))
    · exact (continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by dsimp; linarith))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hv'.le _) (abs_nonneg _)),
      norm_div, norm_cpow_eq_rpow_re_of_pos hv']
    simp only [ofReal_one, neg_re, div_ofNat_re, one_re]
    have hsub : (l + v)⁻¹ - (1 + v)⁻¹ = (1 - l) / ((l + v) * (1 + v)) := by
      field_simp; ring
    rw [hsub, abs_div, abs_of_pos (by positivity : 0 < (l + v) * (1 + v))]
    have hn : ‖(1 : ℂ) + v‖ = 1 + v := by
      rw [show (1 : ℂ) + v = ((1 + v : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    rw [hn]
    have hp : 0 < v ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hv' _
    rw [show v ^ (-(1 / 2 : ℝ)) * (|1 - l| / ((l + v) * (1 + v))) =
        |1 - l| * (v ^ (-(1 / 2 : ℝ)) / (1 + v)) / (l + v) by field_simp,
      show |1 - l| / l * (v ^ (-(1 / 2 : ℝ)) / (1 + v)) =
        |1 - l| * (v ^ (-(1 / 2 : ℝ)) / (1 + v)) / l by ring]
    exact div_le_div_of_nonneg_left (by positivity) hl (by linarith)

/-- **The resolvent integral on the imaginary axis.**  For `λ > 0` and real `u ≠ 0`,
`∫₀^∞ v^{-iu} (1 / (λ + v) - 1 / (1 + v)) dv = -(π / sin (-iπu)) (λ^{-iu} - 1)`.
Area-law manuscript, proof of Lemma 5.2, `04-conditional.tex`, lines 416–420. -/
theorem integral_cpow_imag_mul_inv_sub {l : ℝ} (hl : 0 < l) {u : ℝ} (hu : u ≠ 0) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (-(u * I)) * (((l + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) =
      -(π / sin (π * (-(u * I)))) * ((l : ℂ) ^ (-(u * I)) - 1) := by
  set w : ℂ := -(u * I)
  set g : ℝ → ℝ := fun v => (l + v)⁻¹ - (1 + v)⁻¹
  have hw : w.re = 0 := by simp [w]
  -- the approximating exponents `w - ε`
  have hz1 : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) (1 / 2) → -1 < (w - ε).re := by
    intro ε hε; simp only [sub_re, hw, ofReal_re]; linarith [hε.2]
  have hz0 : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) (1 / 2) → (w - ε).re < 0 := by
    intro ε hε; simp only [sub_re, hw, ofReal_re]; linarith [hε.1]
  have hIoo : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  -- the right-hand side is continuous at `w`
  have hsin : sin (π * w) ≠ 0 := by
    rw [show (π : ℂ) * w = -(((π * u : ℝ) : ℂ) * I) by simp [w]; ring, sin_neg, neg_ne_zero,
      sin_mul_I, mul_ne_zero_iff]
    refine ⟨?_, I_ne_zero⟩
    rw [← ofReal_sinh, ofReal_ne_zero, Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hu
  have hRHS : Filter.Tendsto (fun ε : ℝ => -(π / sin (π * (w - ε))) * ((l : ℂ) ^ (w - ε) - 1))
      (𝓝[>] 0) (𝓝 (-(π / sin (π * w)) * ((l : ℂ) ^ w - 1))) := by
    have hl0 : (l : ℂ) ≠ 0 := ofReal_ne_zero.2 hl.ne'
    have : NeZero (l : ℂ) := ⟨hl0⟩
    have hc : ContinuousAt (fun ε : ℝ => -(π / sin (π * (w - ε))) * ((l : ℂ) ^ (w - ε) - 1)) 0 := by
      have hs : ContinuousAt (fun ε : ℝ => sin (π * (w - ε))) 0 := by fun_prop
      have hs0 : sin (π * (w - ((0 : ℝ) : ℂ))) ≠ 0 := by simpa using hsin
      refine ContinuousAt.mul (ContinuousAt.neg (continuousAt_const.div hs hs0)) ?_
      refine ContinuousAt.sub ?_ continuousAt_const
      exact (continuous_const_cpow (l : ℂ)).continuousAt.comp (by fun_prop)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  -- the left-hand side converges by dominated convergence
  have hbound := integrableOn_rpow_mul_abs_inv_sub hl
  have hgint : IntegrableOn (fun v : ℝ => |g v|) (Ioi 0) :=
    (integral_inv_add_sub_inv_one_add hl).1.abs
  have hLHS : Filter.Tendsto (fun ε : ℝ => ∫ v in Ioi (0 : ℝ),
      (v : ℂ) ^ (w - ε) * ((g v : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (∫ v in Ioi (0 : ℝ), (v : ℂ) ^ w * ((g v : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => |g v| + v ^ (-(1 / 2 : ℝ)) * |g v|) ?_ ?_ (hgint.add hbound) ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
      · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hv'.ne'))
      · refine Complex.continuous_ofReal.continuousAt.comp (ContinuousAt.sub ?_ ?_)
        · exact (continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by dsimp; linarith))
        · exact (continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by dsimp; linarith))
    · filter_upwards [hIoo] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
      have hv' : (0 : ℝ) < v := hv
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hv', norm_real, Real.norm_eq_abs]
      simp only [sub_re, hw, ofReal_re, zero_sub]
      have hle : v ^ (-ε) ≤ 1 + v ^ (-(1 / 2 : ℝ)) := by
        rcases le_total v 1 with h | h
        · have := Real.rpow_le_rpow_of_exponent_ge hv' h (by linarith [hε.2] : -(1 / 2 : ℝ) ≤ -ε)
          linarith [Real.rpow_pos_of_pos hv' (-(1 / 2 : ℝ))]
        · have := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith [hε.1] : -ε ≤ 0)
          linarith [Real.rpow_pos_of_pos hv' (-(1 / 2 : ℝ))]
      calc v ^ (-ε) * |g v| ≤ (1 + v ^ (-(1 / 2 : ℝ))) * |g v| :=
            mul_le_mul_of_nonneg_right hle (abs_nonneg _)
        _ = |g v| + v ^ (-(1 / 2 : ℝ)) * |g v| := by ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
      have hv' : (0 : ℝ) < v := hv
      have hc : ContinuousAt (fun ε : ℝ => (v : ℂ) ^ (w - ε) * ((g v : ℝ) : ℂ)) 0 := by
        have : NeZero (v : ℂ) := ⟨ofReal_ne_zero.2 hv'.ne'⟩
        exact ((continuous_const_cpow (v : ℂ)).continuousAt.comp (by fun_prop)).mul
          continuousAt_const
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have heq : (fun ε : ℝ => ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - ε) * ((g v : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => -(π / sin (π * (w - ε))) * ((l : ℂ) ^ (w - ε) - 1)) := by
    filter_upwards [hIoo] with ε hε
    exact integral_cpow_mul_inv_sub hl (hz1 ε hε) (hz0 ε hε)
  exact tendsto_nhds_unique (hLHS.congr' heq) hRHS

end Complex
