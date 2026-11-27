/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Wendel's inequalities for ratios of Gamma values

For `x > 0` and `0 ≤ s ≤ 1`, log-convexity of the Gamma function gives

`x (x + s)^(s - 1) ≤ Γ(x + s) / Γ(x) ≤ x^s`,

the inequalities of Wendel (1948). For `x ≥ 1` they give `|Γ(x + s)/Γ(x) - x^s| ≤ s`.
These are the gamma-ratio estimates used for the marked ratios of the replica metrics in the
area-law paper (*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 410–413: "Gamma ratios give `r_{λ,i} ≍ ((l_i + 1)/k)^t`").

## Main declarations

* `Real.Gamma_add_le_rpow_mul_Gamma` — `Γ(x + s) ≤ x^s Γ(x)`.
* `Real.mul_Gamma_le_rpow_mul_Gamma_add` — `x Γ(x) ≤ (x + s)^(1 - s) Γ(x + s)`.
* `Real.rpow_sub_le_Gamma_add_div_Gamma` — `x^s - s ≤ Γ(x + s)/Γ(x)` for `x ≥ 1`.
* `Real.integrableOn_rpow_mul_one_add_rpow`, `Real.integral_rpow_mul_one_add_rpow`: the Beta
  integral on the half-line.
-/

section GammaRatio

open Real

namespace Real

variable {x s : ℝ}

/-- **Wendel's upper inequality**: `Γ(x + s) ≤ x^s Γ(x)` for `x > 0` and `0 ≤ s ≤ 1`. -/
theorem Gamma_add_le_rpow_mul_Gamma (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Gamma (x + s) ≤ x ^ s * Gamma x := by
  have hG := Gamma_pos_of_pos hx
  rcases hs0.eq_or_lt with rfl | hs0
  · simp
  rcases hs1.eq_or_lt with rfl | hs1
  · rw [rpow_one, Gamma_add_one hx.ne']
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1) (a := 1 - s)
    (b := s) hx (by linarith) (by linarith) hs0 (by ring)
  have he : (1 - s) * x + s * (x + 1) = x + s := by ring
  rw [he, Gamma_add_one hx.ne', mul_rpow hx.le hG.le] at h
  calc Gamma (x + s) ≤ Gamma x ^ (1 - s) * (x ^ s * Gamma x ^ s) := h
    _ = x ^ s * (Gamma x ^ (1 - s) * Gamma x ^ s) := by ring
    _ = x ^ s * Gamma x := by rw [← rpow_add hG]; simp

/-- **Wendel's lower inequality**: `x Γ(x) ≤ (x + s)^(1 - s) Γ(x + s)` for `x > 0` and
`0 ≤ s ≤ 1`. -/
theorem mul_Gamma_le_rpow_mul_Gamma_add (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x * Gamma x ≤ (x + s) ^ (1 - s) * Gamma (x + s) := by
  rcases hs0.eq_or_lt with rfl | hs0
  · simp
  rcases hs1.eq_or_lt with rfl | hs1
  · rw [sub_self, rpow_zero, one_mul, Gamma_add_one hx.ne']
  have hxs : 0 < x + s := by linarith
  have hG := Gamma_pos_of_pos hxs
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + s) (t := x + s + 1)
    (a := s) (b := 1 - s) hxs (by linarith) hs0 (by linarith) (by ring)
  have he : s * (x + s) + (1 - s) * (x + s + 1) = x + 1 := by ring
  rw [he, Gamma_add_one hx.ne', Gamma_add_one hxs.ne', mul_rpow hxs.le hG.le] at h
  calc x * Gamma x ≤ Gamma (x + s) ^ s * ((x + s) ^ (1 - s) * Gamma (x + s) ^ (1 - s)) := h
    _ = (x + s) ^ (1 - s) * (Gamma (x + s) ^ s * Gamma (x + s) ^ (1 - s)) := by ring
    _ = (x + s) ^ (1 - s) * Gamma (x + s) := by rw [← rpow_add hG]; simp

/-- Wendel's upper inequality in ratio form: `Γ(x + s)/Γ(x) ≤ x^s`. -/
theorem Gamma_add_div_Gamma_le_rpow (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Gamma (x + s) / Gamma x ≤ x ^ s :=
  (div_le_iff₀ (Gamma_pos_of_pos hx)).mpr (Gamma_add_le_rpow_mul_Gamma hx hs0 hs1)

/-- Wendel's lower inequality in ratio form: `x / (x + s)^(1 - s) ≤ Γ(x + s)/Γ(x)`. -/
theorem div_rpow_le_Gamma_add_div_Gamma (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x / (x + s) ^ (1 - s) ≤ Gamma (x + s) / Gamma x := by
  have hxs : 0 < (x + s) ^ (1 - s) := rpow_pos_of_pos (by linarith) _
  rw [div_le_div_iff₀ hxs (Gamma_pos_of_pos hx)]
  linarith [mul_Gamma_le_rpow_mul_Gamma_add hx hs0 hs1]

/-- For `x ≥ 1` and `0 ≤ s ≤ 1`, `x^s - s ≤ Γ(x + s)/Γ(x)`. Together with
`Gamma_add_div_Gamma_le_rpow`, `|Γ(x + s)/Γ(x) - x^s| ≤ s`. -/
theorem rpow_sub_le_Gamma_add_div_Gamma (hx : 1 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ s - s ≤ Gamma (x + s) / Gamma x := by
  have hx0 : 0 < x := by linarith
  have hxs : 0 < x + s := by linarith
  refine le_trans ?_ (div_rpow_le_Gamma_add_div_Gamma hx0 hs0 hs1)
  -- `(x + s)^(1 - s) = (x + s) / (x + s)^s ≤ (x + s) / x^s`.
  have hpow : (x + s) ^ (1 - s) = (x + s) / (x + s) ^ s := by
    rw [rpow_sub hxs, rpow_one]
  have hxs_pow : x ^ s ≤ (x + s) ^ s := rpow_le_rpow hx0.le (by linarith) hs0
  have hxpow_pos : 0 < x ^ s := rpow_pos_of_pos hx0 _
  have hxpow_le : x ^ s ≤ x := by
    simpa using rpow_le_rpow_of_exponent_le hx hs1
  rw [hpow, div_div_eq_mul_div, le_div_iff₀ hxs]
  -- `(x^s - s)(x + s) ≤ x x^s ≤ x (x + s)^s`.
  nlinarith [mul_le_mul_of_nonneg_left hxs_pow hx0.le]

end Real

end GammaRatio

section BetaHalfLine

/-!
## The Beta integral on the half-line

For `a, b > 0`,

`∫_0^∞ u^{a-1} (1 + u)^{-(a+b)} du = Γ(a) Γ(b) / Γ(a + b)`.

This is the Beta integral `B(a, b) = ∫_0^1 x^{a-1} (1 - x)^{b-1} dx`, transported to the
half-line by the substitution `x = u/(1 + u)`. It evaluates the radial integral in the gamma
computation of the proof of Lemma 6.2 of the area-law paper (*A two-dimensional area law from
a global spectral gap*, `05-replicas.tex`, lines 347–364).

The proof is written from the standard theory; no Lean source was adapted.

### Main declarations

* `Real.integrableOn_rpow_mul_one_add_rpow` — integrability on `(0, ∞)`.
* `Real.integral_rpow_mul_one_add_rpow` — the value.
-/

open MeasureTheory Set

namespace Real

/-- The substitution `x = u/(1 + u)`. -/
private noncomputable def betaSub (u : ℝ) : ℝ := u / (1 + u)

private noncomputable def betaSubDeriv (u : ℝ) : ℝ := 1 / (1 + u) ^ 2

private theorem hasDerivWithinAt_betaSub :
    ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt betaSub (betaSubDeriv u) (Ioi (0 : ℝ)) u := by
  intro u hu
  have hu' : (0 : ℝ) < u := hu
  have h1u : (1 : ℝ) + u ≠ 0 := by positivity
  have hd : HasDerivAt (fun u : ℝ => 1 + u) (0 + 1) u :=
    (hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)
  have hquot : HasDerivAt betaSub (((1 : ℝ) * (1 + u) - u * (0 + 1)) / (1 + u) ^ 2) u :=
    (hasDerivAt_id u).div hd h1u
  have heq : ((1 : ℝ) * (1 + u) - u * (0 + 1)) / (1 + u) ^ 2 = betaSubDeriv u := by
    simp only [betaSubDeriv]; congr 1; ring
  rw [heq] at hquot
  exact hquot.hasDerivWithinAt

private theorem injOn_betaSub : InjOn betaSub (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  simp only [betaSub] at hab
  have h1a : (0 : ℝ) < 1 + a := by have : (0 : ℝ) < a := ha; linarith
  have h1b : (0 : ℝ) < 1 + b := by have : (0 : ℝ) < b := hb; linarith
  field_simp at hab
  nlinarith [hab]

private theorem image_betaSub : betaSub '' (Ioi (0 : ℝ)) = Ioo (0 : ℝ) 1 := by
  ext x
  simp only [mem_image, mem_Ioi, mem_Ioo, betaSub]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h1u : (0 : ℝ) < 1 + u := by linarith
    exact ⟨by positivity, by rw [div_lt_one h1u]; linarith⟩
  · intro ⟨hx0, hx1⟩
    refine ⟨x / (1 - x), by have : (0 : ℝ) < 1 - x := by linarith
                            positivity, ?_⟩
    have h1x : (0 : ℝ) < 1 - x := by linarith
    have hden : (1 : ℝ) + x / (1 - x) = 1 / (1 - x) := by field_simp; ring
    rw [hden]; field_simp

/-- The Beta integrand after the substitution. -/
private theorem betaSub_integrand {a b u : ℝ} (hu : 0 < u) :
    |betaSubDeriv u| • (betaSub u ^ (a - 1) * (1 - betaSub u) ^ (b - 1)) =
      u ^ (a - 1) * (1 + u) ^ (-(a + b)) := by
  have h1u : (0 : ℝ) < 1 + u := by linarith
  simp only [betaSub, betaSubDeriv, smul_eq_mul]
  rw [abs_of_nonneg (by positivity)]
  have h1mx : (1 : ℝ) - u / (1 + u) = 1 / (1 + u) := by field_simp; ring
  rw [h1mx, div_rpow hu.le h1u.le, div_rpow one_pos.le h1u.le, one_rpow]
  have e2 : ((1 + u) ^ 2 : ℝ) = (1 + u) ^ (2 : ℝ) := by rw [rpow_two]
  rw [e2]
  have : (1 + u) ^ (-(a + b)) = 1 / ((1 + u) ^ (2 : ℝ) * (1 + u) ^ (a - 1) *
      (1 + u) ^ (b - 1)) := by
    rw [← rpow_add h1u, ← rpow_add h1u, one_div, ← rpow_neg h1u.le]
    congr 1; ring
  rw [this]
  field_simp

/-- The half-line Beta integrand is integrable. -/
theorem integrableOn_rpow_mul_one_add_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * (1 + u) ^ (-(a + b))) (Ioi 0) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) (Ioo 0 1) := by
    have h := Complex.betaIntegral_convergent (u := a) (v := b) (by simpa using ha)
      (by simpa using hb)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
    have h' : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)‖)
        (Ioo 0 1) := h.norm
    refine IntegrableOn.congr_fun h' (fun x hx => ?_) measurableSet_Ioo
    obtain ⟨hx0, hx1⟩ := hx
    simp only [Complex.norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hx0)]
    rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp
  rw [← image_betaSub] at hint
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hasDerivWithinAt_betaSub injOn_betaSub] at hint
  exact hint.congr_fun (fun u hu => betaSub_integrand hu) measurableSet_Ioi

/-- **The Beta integral on the half-line**:
`∫_0^∞ u^{a-1} (1 + u)^{-(a+b)} du = Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_rpow_mul_one_add_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), u ^ (a - 1) * (1 + u) ^ (-(a + b)) =
      Gamma a * Gamma b / Gamma (a + b) := by
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    hasDerivWithinAt_betaSub injOn_betaSub (fun x => x ^ (a - 1) * (1 - x) ^ (b - 1))
  rw [image_betaSub] at hcov
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun u hu => betaSub_integrand hu), ← hcov]
  -- the real Beta integral
  have hbeta : ((∫ x in Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) =
      Complex.betaIntegral a b := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    obtain ⟨hx0, hx1⟩ := hx
    push_cast
    rw [Complex.ofReal_cpow hx0.le, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - x)]
    push_cast
    ring_nf
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := a) (t := b) (by simpa using ha)
    (by simpa using hb)
  have hne : Complex.Gamma (a + b) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  apply Complex.ofReal_injective
  rw [hbeta]
  push_cast
  rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
  push_cast
  rw [eq_div_iff hne, mul_comm, ← hG]

end Real

end BetaHalfLine
