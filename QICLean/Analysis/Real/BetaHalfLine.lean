/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Beta integral on the half-line

For `a, b > 0`,

`∫_0^∞ u^{a-1} (1 + u)^{-(a+b)} du = Γ(a) Γ(b) / Γ(a + b)`.

This is the Beta integral `B(a, b) = ∫_0^1 x^{a-1} (1 - x)^{b-1} dx`, transported to the
half-line by the substitution `x = u/(1 + u)`. It evaluates the radial integral in the gamma
computation of the proof of Lemma 6.2 of the area-law paper (*A two-dimensional area law from
a global spectral gap*, `05-replicas.tex`, lines 347–364).

The proof is written from the standard theory; no Lean source was adapted.

## Main declarations

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
