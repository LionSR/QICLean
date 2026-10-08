/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ResolventDefectIntegral

/-!
# Imaginary powers of a compression and the resolvent discrepancy

For a resolvent compression `A, B, V, b₀` with `a₀ = V b₀`, the **phase gap** at a
complex exponent `z` is `A^z a₀ - V B^z b₀`.  For real `u ≠ 0` and `w = -iu`,
$$A^{w}a_0-VB^{w}b_0=-\frac{\sin\pi w}{\pi}\int_0^\infty v^{w}\delta_v\,dv$$
in every coordinate direction, so
$$\lVert A^{-iu}a_0-VB^{-iu}b_0\rVert\le\frac{|\sinh\pi u|}{\pi}
  \int_0^\infty\sqrt{h(v)/v}\,dv,$$
provided the right-hand integrand is integrable.

## Main definitions

* `Matrix.ResolventCompression.phaseGap` — `A^z a₀ - V B^z b₀`.

## Main results

* `Matrix.ResolventCompression.norm_phaseGap_le` — the phase gap on the imaginary axis is
  bounded by `|sinh π u| / π · ∫₀^∞ √(h(v) / v) dv`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 410–423.
-/

open MeasureTheory Set Filter Topology
open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The sesquilinear form of a spectral function in eigencoordinates:
`⟨y, f(A) x⟩ = ∑ₖ f(λₖ) conj((U* y)ₖ) (U* x)ₖ`. -/
theorem dotProduct_spectralFun_mulVec' (U : unitary (Matrix n n ℂ)) (f : n → ℂ)
    (y x : n → ℂ) :
    star y ⬝ᵥ (spectralFun U f *ᵥ x) =
      ∑ k, f k * (star (star (U : Matrix n n ℂ) *ᵥ y) k * (star (U : Matrix n n ℂ) *ᵥ x) k) := by
  have hx : star y ⬝ᵥ (spectralFun U f *ᵥ x) =
      star (star (U : Matrix n n ℂ) *ᵥ y) ⬝ᵥ (diagonal f *ᵥ (star (U : Matrix n n ℂ) *ᵥ x)) := by
    simp only [spectralFun, ← mulVec_mulVec]
    rw [dotProduct_mulVec, star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [hx]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

namespace ResolventCompression

variable (R : ResolventCompression n m)

/-- The phase gap `A^z a₀ - V B^z b₀`.  Area-law manuscript, `04-conditional.tex`,
lines 410–415. -/
def phaseGap (z : ℂ) : n → ℂ :=
  spectralFun R.UA (fun k => (R.lam k : ℂ) ^ z) *ᵥ R.a0 -
    R.V *ᵥ (spectralFun R.UB (fun j => (R.mu j : ℂ) ^ z) *ᵥ R.b0)

/-- The coefficients of `⟨u, f(A) a₀⟩` in eigencoordinates. -/
def coeffA (u : n → ℂ) (k : n) : ℂ :=
  star (star (R.UA : Matrix n n ℂ) *ᵥ u) k * (star (R.UA : Matrix n n ℂ) *ᵥ R.a0) k

/-- The coefficients of `⟨u, V f(B) b₀⟩` in eigencoordinates. -/
def coeffB (u : n → ℂ) (j : m) : ℂ :=
  star (star (R.UB : Matrix m m ℂ) *ᵥ (R.Vᴴ *ᵥ u)) j * (star (R.UB : Matrix m m ℂ) *ᵥ R.b0) j

theorem dotProduct_spectral_sub (u : n → ℂ) (f : ℝ → ℂ) :
    star u ⬝ᵥ (spectralFun R.UA (fun k => f (R.lam k)) *ᵥ R.a0 -
        R.V *ᵥ (spectralFun R.UB (fun j => f (R.mu j)) *ᵥ R.b0)) =
      ∑ k, f (R.lam k) * R.coeffA u k - ∑ j, f (R.mu j) * R.coeffB u j := by
  rw [dotProduct_sub, dotProduct_spectralFun_mulVec',
    show star u ⬝ᵥ (R.V *ᵥ (spectralFun R.UB (fun j => f (R.mu j)) *ᵥ R.b0)) =
      star (R.Vᴴ *ᵥ u) ⬝ᵥ (spectralFun R.UB (fun j => f (R.mu j)) *ᵥ R.b0) by
        rw [star_mulVec_dotProduct, conjTranspose_conjTranspose],
    dotProduct_spectralFun_mulVec']
  rfl

theorem sum_coeffA_eq_sum_coeffB (u : n → ℂ) :
    ∑ k, R.coeffA u k = ∑ j, R.coeffB u j := by
  have h := R.dotProduct_spectral_sub u (fun _ => 1)
  simp only [spectralFun_one, one_mulVec, one_mul] at h
  rw [a0, sub_self, dotProduct_zero] at h
  exact sub_eq_zero.1 h.symm

theorem dotProduct_discrepancy (u : n → ℂ) (v : ℝ) :
    star u ⬝ᵥ R.discrepancy v =
      ∑ k, (((R.lam k + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) * R.coeffA u k -
        ∑ j, (((R.mu j + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) * R.coeffB u j := by
  have h := R.dotProduct_spectral_sub u (fun t => ((t + v)⁻¹ : ℝ))
  rw [discrepancy, ← resA, ← resB] at *
  rw [h]
  have hs := R.sum_coeffA_eq_sum_coeffB u
  simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  ring

theorem dotProduct_phaseGap (u : n → ℂ) (z : ℂ) :
    star u ⬝ᵥ R.phaseGap z =
      ∑ k, ((R.lam k : ℂ) ^ z - 1) * R.coeffA u k - ∑ j, ((R.mu j : ℂ) ^ z - 1) * R.coeffB u j := by
  have h := R.dotProduct_spectral_sub u (fun t => (t : ℂ) ^ z)
  rw [phaseGap, h]
  have hs := R.sum_coeffA_eq_sum_coeffB u
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hs]
  ring

/-- **Integral representation of the phase gap on the imaginary axis.**  For real
`u ≠ 0` and `w = -iu`,
`⟨x, A^w a₀ - V B^w b₀⟩ = -(sin π w / π) ∫₀^∞ v^w ⟨x, δ_v⟩ dv`.
Area-law manuscript, `04-conditional.tex`, lines 410–420. -/
theorem dotProduct_phaseGap_eq_integral (x : n → ℂ) {u : ℝ} (hu : u ≠ 0) :
    star x ⬝ᵥ R.phaseGap (-(u * Complex.I)) =
      -(Complex.sin (Real.pi * (-(u * Complex.I))) / Real.pi) *
        ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (-(u * Complex.I)) * (star x ⬝ᵥ R.discrepancy v) := by
  set w : ℂ := -(u * Complex.I)
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    rw [show (Real.pi : ℂ) * w = -(((Real.pi * u : ℝ) : ℂ) * Complex.I) by simp [w]; ring,
      Complex.sin_neg, neg_ne_zero, Complex.sin_mul_I, mul_ne_zero_iff]
    refine ⟨?_, Complex.I_ne_zero⟩
    rw [← Complex.ofReal_sinh, Complex.ofReal_ne_zero, Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hu
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hint : ∀ l : ℝ, 0 < l → IntegrableOn
      (fun v : ℝ => (v : ℂ) ^ w * (((l + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ)) (Ioi 0) := by
    intro l hl
    refine ((integral_inv_add_sub_inv_one_add hl).1.norm).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
      · exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hv'.ne')
      · refine Complex.continuous_ofReal.continuousAt.comp (ContinuousAt.sub ?_ ?_)
        · exact (continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by dsimp; linarith))
        · exact (continuousAt_const.add continuousAt_id).inv₀ (ne_of_gt (by dsimp; linarith))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
      have hv' : (0 : ℝ) < v := hv
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv', Complex.norm_real]
      simp [w]
  have hval : ∀ l : ℝ, 0 < l → ∫ v in Ioi (0 : ℝ),
      (v : ℂ) ^ w * (((l + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ) =
        -(Real.pi / Complex.sin (Real.pi * w)) * ((l : ℂ) ^ w - 1) :=
    fun l hl => Complex.integral_cpow_imag_mul_inv_sub hl hu
  have hexp : ∀ v : ℝ, (v : ℂ) ^ w * (star x ⬝ᵥ R.discrepancy v) =
      ∑ k, R.coeffA x k * ((v : ℂ) ^ w * (((R.lam k + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ)) -
        ∑ j, R.coeffB x j * ((v : ℂ) ^ w * (((R.mu j + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ)) := by
    intro v
    rw [R.dotProduct_discrepancy, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
  simp only [hexp]
  have hA : ∀ k, IntegrableOn (fun v : ℝ => R.coeffA x k *
      ((v : ℂ) ^ w * (((R.lam k + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ))) (Ioi 0) :=
    fun k => (hint _ (R.lam_pos k)).const_mul _
  have hB : ∀ j, IntegrableOn (fun v : ℝ => R.coeffB x j *
      ((v : ℂ) ^ w * (((R.mu j + v)⁻¹ - (1 + v)⁻¹ : ℝ) : ℂ))) (Ioi 0) :=
    fun j => (hint _ (R.mu_pos j)).const_mul _
  rw [integral_sub (integrable_finsetSum _ fun k _ => hA k)
      (integrable_finsetSum _ fun j _ => hB j),
    integral_finsetSum _ fun k _ => hA k, integral_finsetSum _ fun j _ => hB j]
  simp only [integral_const_mul, hval _ (R.lam_pos _), hval _ (R.mu_pos _)]
  rw [R.dotProduct_phaseGap]
  simp only [mul_sub, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> field_simp

end ResolventCompression

end Matrix

end
