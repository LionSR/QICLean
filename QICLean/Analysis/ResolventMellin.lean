/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

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

open MeasureTheory Set
open scoped Real

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

end Complex
