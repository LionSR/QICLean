/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import QICLean.Analysis.GaussianFilter.Kernel

/-!
# The Gaussian–Cauchy transform and the negative-frequency cutoff

For a positive regularizer `ε`, the Cauchy denominator `ε - it` has the half-line Laplace
representation `(ε - it)⁻¹ = ∫_{s>0} e^{(-ε + it)s} ds`, and its product with a Gaussian
characteristic phase is absolutely integrable. Fubini and the Gaussian characteristic function
turn the Gaussian–Cauchy integral `gaussianCauchyTransform h ε ω` into a damped half-line
Gaussian, and as `ε → 0⁺`, multiplied by the Gaussian density at zero, it tends to the right tail
`γ_{1/h}([ω, ∞))` of the centred Gaussian of variance `1/h`.

At variance `Δ²/q` that tail is the cutoff `gaussianNegativeFrequencyCutoff q Δ ω`: it lies in
`[0, 1]`, is at most `e^{-q/2}` at frequencies `ω ≥ Δ`, and is within `e^{-q/2}` of `1` at
`ω ≤ -Δ`; it approximates the selector of negative frequencies. The cutoff time `T = ℓ/(2v)`
balances the short-time propagation exponential and the gap tail, which gives one exponential
clustering rate depending only on the gap and the propagation velocity.

## Main definitions

* `GaussianFilter.gaussianCauchyKernel`, `GaussianFilter.gaussianCauchyTransform`.
* `GaussianFilter.gaussianNegativeFrequencyCutoff`.

## Main results

* `GaussianFilter.inv_cauchyDenominator_eq_integral` — the Laplace representation.
* `GaussianFilter.halfLine_gaussian_integral_eq_measureReal` — the normalization.
* `GaussianFilter.tendsto_normalized_gaussianCauchyTransform`,
  `GaussianFilter.tendsto_normalized_gaussianCauchyTransform_cutoff` — the limit `ε → 0⁺`.
* `GaussianFilter.gaussianNegativeFrequencyCutoff_le_exp_of_gap`,
  `GaussianFilter.abs_one_sub_gaussianNegativeFrequencyCutoff_le_exp_of_gap` — the cutoff at the
  gap.
* `GaussianFilter.exists_gaussianFrequencyClusteringRate` — one exponential clustering rate.

## References

Hastings and Koma, *Spectral gap and exponential decay of correlations*, arXiv:math-ph/0507008,
Section 3, proof of Lemma 3.1.

Moved from TNLean, `TNLean/Lattice/GaussianCauchyKernel.lean`, `GaussianCauchyNormalization.lean`,
`GaussianNegativeFrequencyCutoff.lean`, `GaussianCauchyTransform.lean` and
`GaussianFrequencyClusteringRate.lean` at commit `e113e005`. Changes: namespace `GaussianFilter` in
place of `TNLean.Lattice`.
-/

noncomputable section

section CauchyKernel

open MeasureTheory

namespace GaussianFilter

/-- The regularized negative-frequency time kernel. The rational factor
is \(i/(t+i\varepsilon)=1/(\varepsilon-it)\).
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
def gaussianCauchyKernel (α ε t : ℝ) : ℂ :=
  (Real.exp (-α * t ^ 2) / (2 * Real.pi) : ℝ) *
    ((ε : ℂ) - Complex.I * t)⁻¹

/-- The regularized Cauchy denominator is nonzero at every real time.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
theorem cauchyDenominator_ne_zero {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (ε : ℂ) - Complex.I * t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have : ε = 0 := by simpa using hre
  exact hε.ne' this

/-- The rational Cauchy factor is bounded by the reciprocal of its
positive regularizer. Source: Hastings–Koma, arXiv:math-ph/0507008,
equation (3.8). -/
theorem norm_inv_cauchyDenominator_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖((ε : ℂ) - Complex.I * t)⁻¹‖ ≤ ε⁻¹ := by
  have hnorm : ε ≤ ‖(ε : ℂ) - Complex.I * t‖ := by
    simpa using Complex.re_le_norm ((ε : ℂ) - Complex.I * t)
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hε hnorm

/-- The rational source kernel has a convergent half-line Laplace
representation whenever the regularizer is positive. This is the scalar
identity needed before the Gaussian Fourier interchange.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1. -/
theorem inv_cauchyDenominator_eq_integral {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ((ε : ℂ) - Complex.I * t)⁻¹ =
      ∫ s : ℝ in Set.Ioi 0, Complex.exp ((-(ε : ℂ) + Complex.I * t) * s) := by
  have ha : (-(ε : ℂ) + Complex.I * t).re < 0 := by simpa using neg_lt_zero.mpr hε
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hsign : -(ε : ℂ) + Complex.I * t = -((ε : ℂ) - Complex.I * t) := by ring
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [hsign, neg_div_neg_eq, one_div]

/-- The Gaussian/Cauchy kernel is bounded by an integrable Gaussian
when its regularizer is positive. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.8). -/
theorem norm_gaussianCauchyKernel_le {ε : ℝ} (hε : 0 < ε) (α t : ℝ) :
    ‖gaussianCauchyKernel α ε t‖ ≤
      (2 * Real.pi * ε)⁻¹ * Real.exp (-α * t ^ 2) := by
  rw [gaussianCauchyKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.exp (-α * t ^ 2) / (2 * Real.pi)) * ε⁻¹ :=
      mul_le_mul_of_nonneg_left (norm_inv_cauchyDenominator_le hε t) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero, hε.ne']

/-- Multiplying the regularized kernel by the frequency phase
preserves absolute integrability. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.8). -/
theorem integrable_gaussianCauchyKernel_mul_exp {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (ω : ℝ) :
    Integrable (fun t : ℝ ↦ gaussianCauchyKernel α ε t *
      Complex.exp (Complex.I * ω * t)) := by
  have hcont : Continuous fun t : ℝ ↦ gaussianCauchyKernel α ε t *
      Complex.exp (Complex.I * ω * t) := by
    unfold gaussianCauchyKernel
    apply Continuous.mul
    · apply Continuous.mul
      · exact Complex.continuous_ofReal.comp (by fun_prop)
      · exact (by fun_prop : Continuous fun t : ℝ ↦ (ε : ℂ) - Complex.I * t).inv₀
          (cauchyDenominator_ne_zero hε)
    · fun_prop
  apply ((integrable_exp_neg_mul_sq hα).const_mul (2 * Real.pi * ε)⁻¹).mono'
    hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hphase : ‖Complex.exp (Complex.I * ω * t)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [norm_mul, hphase, mul_one]
  exact norm_gaussianCauchyKernel_le hε α t

/-- A finite explicit bound for the regularized frequency integral.
Its dependence on the regularizer is retained; this is not a uniform
regularizer-limit or locality bound. Source: Hastings–Koma,
arXiv:math-ph/0507008, equation (3.8). -/
theorem norm_integral_gaussianCauchyKernel_mul_exp_le {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (ω : ℝ) :
    ‖∫ t : ℝ, gaussianCauchyKernel α ε t * Complex.exp (Complex.I * ω * t)‖ ≤
      (2 * Real.pi * ε)⁻¹ * Real.sqrt (Real.pi / α) := by
  have hnorm (t : ℝ) :
      ‖gaussianCauchyKernel α ε t * Complex.exp (Complex.I * ω * t)‖ ≤
        (2 * Real.pi * ε)⁻¹ * Real.exp (-α * t ^ 2) := by
    have hphase : ‖Complex.exp (Complex.I * ω * t)‖ = 1 := by
      simp [Complex.norm_exp]
    rw [norm_mul, hphase, mul_one]
    exact norm_gaussianCauchyKernel_le hε α t
  calc
    _ ≤ ∫ t : ℝ, (2 * Real.pi * ε)⁻¹ * Real.exp (-α * t ^ 2) :=
      norm_integral_le_of_norm_le
        ((integrable_exp_neg_mul_sq hα).const_mul _) (Filter.Eventually.of_forall hnorm)
    _ = _ := by rw [integral_const_mul, integral_gaussian α]

end GaussianFilter

end CauchyKernel

section CauchyNormalization

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace GaussianFilter

/-- Normalize the half-line frequency integral to the centered
Gaussian tail of inverse variance. No density, integral or normalization
identity is supplied as a premise. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equations (3.7)–(3.13). -/
theorem halfLine_gaussian_integral_eq_measureReal
    (h : ℝ≥0) (hh : 0 < h) (ω : ℝ) :
    (kernel h⁻¹ 0 : ℂ) *
        (∫ s : ℝ in Set.Ioi 0,
          Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2)) =
      ((gaussianReal 0 h⁻¹).real (Set.Ici ω) : ℂ) := by
  have hhReal : 0 < (h : ℝ) := by exact_mod_cast hh
  have hdensity (t : ℝ) :
      (kernel h⁻¹ t : ℂ) = (kernel h⁻¹ 0 : ℂ) *
        Complex.exp (-(h : ℂ) * (t : ℂ) ^ 2 / 2) := by
    have hexponent : -t ^ 2 / (2 * ((h⁻¹ : ℝ≥0) : ℝ)) =
        -(h : ℝ) * t ^ 2 / 2 := by
      rw [NNReal.coe_inv]
      field_simp [hhReal.ne']
    have hreal : kernel h⁻¹ t = kernel h⁻¹ 0 *
        Real.exp (-(h : ℝ) * t ^ 2 / 2) := by
      simp only [kernel_eq, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div,
        Real.exp_zero, mul_one, hexponent]
    have hcast : -(h : ℂ) * (t : ℂ) ^ 2 / 2 =
        ((-(h : ℝ) * t ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hreal, Complex.ofReal_mul, hcast, Complex.ofReal_exp]
  have htranslate :
      (∫ s : ℝ in Set.Ioi 0, (kernel h⁻¹ (ω + s) : ℂ)) =
        ∫ t : ℝ in Set.Ioi ω, (kernel h⁻¹ t : ℂ) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    calc
      _ = ∫ s : ℝ, (Set.Ioi ω).indicator (fun t ↦ (kernel h⁻¹ t : ℂ)) (ω + s) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s ↦ by
          simp only [Set.indicator, Set.mem_Ioi, lt_add_iff_pos_right]
      _ = _ := integral_add_left_eq_self
        ((Set.Ioi ω).indicator (fun t ↦ (kernel h⁻¹ t : ℂ))) ω
  calc
    _ = ∫ s : ℝ in Set.Ioi 0, (kernel h⁻¹ (ω + s) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s ↦ (hdensity (ω + s)).symm
    _ = ∫ t : ℝ in Set.Ioi ω, (kernel h⁻¹ t : ℂ) := htranslate
    _ = Complex.ofReal (∫ t : ℝ in Set.Ici ω, kernel h⁻¹ t) := by
      rw [← integral_Ici_eq_integral_Ioi]
      exact _root_.integral_complex_ofReal
    _ = _ := congrArg Complex.ofReal
      (integral_kernel_eq_measureReal (inv_ne_zero hh.ne') (Set.Ici ω))

end GaussianFilter

end CauchyNormalization

section NegativeFrequencyCutoff

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace GaussianFilter

/-- The Gaussian approximation to the negative-frequency step. Its
variance is \(\Delta^2/q\), so the gap tails have the source rate
\(e^{-q/2}\). Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equation (3.7). -/
def gaussianNegativeFrequencyCutoff (q Δ ω : ℝ) : ℝ :=
  (gaussianReal 0 (Δ ^ 2 / q).toNNReal).real (Set.Ici ω)

private theorem gaussian_gap_rate {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) :
    Real.exp (-(Δ ^ 2) / (2 * ((Δ ^ 2 / q).toNNReal : ℝ))) =
      Real.exp (-q / 2) := by
  congr 1
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg Δ) hq.le)]
  field_simp [hq.ne', hΔ.ne']

/-- The Gaussian frequency multiplier is nonnegative.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.7). -/
theorem gaussianNegativeFrequencyCutoff_nonneg (q Δ ω : ℝ) :
    0 ≤ gaussianNegativeFrequencyCutoff q Δ ω :=
  measureReal_nonneg

/-- The Gaussian frequency multiplier is at most one.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.7). -/
theorem gaussianNegativeFrequencyCutoff_le_one (q Δ ω : ℝ) :
    gaussianNegativeFrequencyCutoff q Δ ω ≤ 1 :=
  measureReal_le_one

/-- Above the positive gap, the Gaussian selector has the
explicit exponential error. The Gaussian tail bound is proved from its
moment-generating function. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem gaussianNegativeFrequencyCutoff_le_exp_of_gap
    {q Δ ω : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (hω : Δ ≤ ω) :
    gaussianNegativeFrequencyCutoff q Δ ω ≤ Real.exp (-q / 2) := by
  let v := (Δ ^ 2 / q).toNNReal
  calc
    (gaussianReal 0 v).real (Set.Ici ω) ≤
        (gaussianReal 0 v).real {x : ℝ | Δ ≤ x} :=
      measureReal_mono fun _ hx ↦ hω.trans hx
    _ ≤ Real.exp (-(Δ ^ 2) / (2 * (v : ℝ))) :=
      (GaussianFilter.hasSubgaussianMGF_gaussianReal v).measure_ge_le hΔ.le
    _ = _ := gaussian_gap_rate hq hΔ

/-- Below the negative gap, the Gaussian selector differs from one
by at most the same explicit exponential error. No symmetry or tail
estimate is assumed: apply the Gaussian moment-generating-function bound
to the negated variable. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem abs_one_sub_gaussianNegativeFrequencyCutoff_le_exp_of_gap
    {q Δ ω : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (hω : ω ≤ -Δ) :
    |1 - gaussianNegativeFrequencyCutoff q Δ ω| ≤ Real.exp (-q / 2) := by
  let v := (Δ ^ 2 / q).toNNReal
  rw [abs_of_nonneg (sub_nonneg.mpr (gaussianNegativeFrequencyCutoff_le_one q Δ ω))]
  calc
    1 - (gaussianReal 0 v).real (Set.Ici ω) =
        (gaussianReal 0 v).real ((Set.Ici ω)ᶜ) :=
      (probReal_compl_eq_one_sub measurableSet_Ici).symm
    _ ≤ (gaussianReal 0 v).real {x : ℝ | Δ ≤ -x} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      have hx' : x < ω := by simpa only [Set.mem_compl_iff, Set.mem_Ici, not_le] using hx
      change Δ ≤ -x
      linarith
    _ ≤ Real.exp (-(Δ ^ 2) / (2 * (v : ℝ))) := by
      simpa only [Pi.neg_apply, id_eq] using
        (GaussianFilter.hasSubgaussianMGF_gaussianReal v).neg.measure_ge_le hΔ.le
    _ = _ := gaussian_gap_rate hq hΔ

end GaussianFilter

end NegativeFrequencyCutoff

section CauchyTransform

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace GaussianFilter

/-- The Gaussian-averaged Cauchy transform, at time variance \(h\),
regularizer \(\varepsilon\), and frequency \(\omega\).
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1. -/
def gaussianCauchyTransform (h : ℝ≥0) (ε ω : ℝ) : ℂ :=
  ∫ t : ℝ, ((ε : ℂ) - Complex.I * t)⁻¹ *
    Complex.exp ((ω : ℂ) * t * Complex.I) ∂gaussianReal 0 h

/-- The Gaussian/Cauchy integral equals its damped half-line
Gaussian transform. Joint absolute integrability is proved from the
positive regularizer; the Gaussian transform is the existing exact
characteristic function. No exchange-of-integrals hypothesis is supplied.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.8)–(3.13), written with the normalized Gaussian time measure. -/
theorem gaussianCauchyTransform_eq_integral (h : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (ω : ℝ) :
    gaussianCauchyTransform h ε ω =
      ∫ s : ℝ in Set.Ioi 0, Complex.exp (-(ε : ℂ) * s) *
        Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2) := by
  let μ : Measure ℝ := gaussianReal 0 h
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℂ := fun t s ↦
    Complex.exp (-(ε : ℂ) * s) * Complex.exp (((ω + s : ℝ) : ℂ) * t * Complex.I)
  have hFNorm (t s : ℝ) : ‖F t s‖ = Real.exp (-ε * s) := by
    simp [F, Complex.norm_exp]
  have hdecay : Integrable (fun s : ℝ ↦ Real.exp (-ε * s)) ν :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0
  have hmajor : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * Real.exp (-ε * p.2))
      (μ.prod ν) :=
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ).mul_prod hdecay
  have hJoint : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply hmajor.mono'
    · apply Continuous.aestronglyMeasurable
      dsimp only [Function.uncurry, F]
      fun_prop
    · exact Filter.Eventually.of_forall fun p ↦ by
        change ‖F p.1 p.2‖ ≤ 1 * Real.exp (-ε * p.2)
        rw [hFNorm, one_mul]
  have hLaplace (t : ℝ) :
      ((ε : ℂ) - Complex.I * t)⁻¹ * Complex.exp ((ω : ℂ) * t * Complex.I) =
        ∫ s, F t s ∂ν := by
    rw [inv_cauchyDenominator_eq_integral hε t, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s ↦ by
      dsimp only [F]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  calc
    gaussianCauchyTransform h ε ω = ∫ t, ∫ s, F t s ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hLaplace
    _ = ∫ s, ∫ t, F t s ∂μ ∂ν := integral_integral_swap hJoint
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s ↦ by
        dsimp only [F]
        rw [integral_const_mul, GaussianFilter.integral_cexp h (ω + s)]

/-- The Gaussian/Cauchy transform has the source half-line Gaussian
limit as the positive regularizer tends to zero. Dominated convergence is
proved with the translated Gaussian as an integrable majorant; the divergent
crude inverse-regularizer bound is not used for this passage.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7),
before converting the Gaussian integral to its normalized tail. -/
theorem tendsto_gaussianCauchyTransform_zero_regularizer
    (h : ℝ≥0) (hh : 0 < h) (ω : ℝ) :
    Filter.Tendsto (fun ε : ℝ ↦ gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s : ℝ in Set.Ioi 0,
        Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let g : ℝ → ℝ := fun s ↦ Real.exp (-(h : ℝ) * (ω + s) ^ 2 / 2)
  let G : ℝ → ℂ := fun s ↦ Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2)
  let F : ℝ → ℝ → ℂ := fun ε s ↦ Complex.exp (-(ε : ℂ) * s) * G s
  have hhReal : 0 < (h : ℝ) := by exact_mod_cast hh
  have hGNorm (s : ℝ) : ‖G s‖ = g s := by
    have hcast : -(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2 =
        ((-(h : ℝ) * (ω + s) ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    dsimp only [G, g]
    rw [hcast, ← Complex.ofReal_exp, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hg : Integrable g ν := by
    have hbase := (integrable_exp_neg_mul_sq (half_pos hhReal)).comp_add_left ω
    have hfull : Integrable g := hbase.congr (Filter.Eventually.of_forall fun s ↦ by
      dsimp only [g]
      congr 1
      ring)
    exact hfull.integrableOn
  have hmeas : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), AEStronglyMeasurable (F ε) ν :=
    Filter.Eventually.of_forall fun ε ↦ by
      apply Continuous.aestronglyMeasurable
      dsimp only [F, G]
      fun_prop
  have hbound : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ s ∂ν, ‖F ε s‖ ≤ g s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hεpos : 0 < ε := hε
    have hspos : 0 < s := hs
    have hdecay : Real.exp (-ε * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hfirst : ‖Complex.exp (-(ε : ℂ) * s)‖ = Real.exp (-ε * s) := by
      simp [Complex.norm_exp]
    dsimp only [F]
    rw [norm_mul, hfirst, hGNorm]
    calc
      _ ≤ 1 * g s := mul_le_mul_of_nonneg_right hdecay (Real.exp_pos _).le
      _ = _ := one_mul _
  have hlim : ∀ᵐ s ∂ν, Filter.Tendsto (fun ε : ℝ ↦ F ε s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (G s)) :=
    Filter.Eventually.of_forall fun s ↦ by
      have hcont : Continuous fun ε : ℝ ↦ F ε s := by dsimp only [F]; fun_prop
      simpa only [F, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using
        (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hint := tendsto_integral_filter_of_dominated_convergence g hmeas hbound hg hlim
  apply hint.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (gaussianCauchyTransform_eq_integral h hε ω).symm

/-- The normalized Gaussian/Cauchy transform converges to the
Gaussian probability tail. Its normalization is the density at zero of
the inverse-variance Gaussian, with no supplied transform identity.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem tendsto_normalized_gaussianCauchyTransform
    (h : ℝ≥0) (hh : 0 < h) (ω : ℝ) :
    Filter.Tendsto (fun ε : ℝ ↦ (GaussianFilter.kernel h⁻¹ 0 : ℂ) *
      gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((gaussianReal 0 h⁻¹).real (Set.Ici ω) : ℂ)) := by
  have hlim := (tendsto_gaussianCauchyTransform_zero_regularizer h hh ω).const_mul
    (GaussianFilter.kernel h⁻¹ 0 : ℂ)
  simpa only [GaussianFilter.halfLine_gaussian_integral_eq_measureReal h hh ω] using hlim

/-- The source Gaussian parameters give the frequency cutoff whose
positive- and negative-gap errors are bounded by \(e^{-q/2}\). This proves
the scalar Cauchy/Gaussian limit identity rather than assuming a Fourier
or approximation premise. Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equation (3.7), with \(\alpha=\Delta^2/(2q)\). -/
theorem tendsto_normalized_gaussianCauchyTransform_cutoff
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (ω : ℝ) :
    let h := (q / Δ ^ 2).toNNReal
    Filter.Tendsto (fun ε : ℝ ↦ (GaussianFilter.kernel h⁻¹ 0 : ℂ) *
      gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussianNegativeFrequencyCutoff q Δ ω : ℂ)) := by
  let h := (q / Δ ^ 2).toNNReal
  have hh : 0 < h := Real.toNNReal_pos.mpr (by positivity)
  have hinv : h⁻¹ = (Δ ^ 2 / q).toNNReal := by
    apply NNReal.coe_injective
    dsimp only [h]
    rw [NNReal.coe_inv, Real.coe_toNNReal _ (div_nonneg hq.le (sq_nonneg Δ)),
      Real.coe_toNNReal _ (div_nonneg (sq_nonneg Δ) hq.le), inv_div]
  have hcut : gaussianNegativeFrequencyCutoff q Δ ω =
      (gaussianReal 0 h⁻¹).real (Set.Ici ω) := by
    rw [gaussianNegativeFrequencyCutoff, hinv]
  change Filter.Tendsto (fun ε : ℝ ↦ (GaussianFilter.kernel h⁻¹ 0 : ℂ) *
    gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
    (nhds (gaussianNegativeFrequencyCutoff q Δ ω : ℂ))
  rw [hcut]
  exact tendsto_normalized_gaussianCauchyTransform h hh ω

end GaussianFilter

end CauchyTransform

section FrequencyClusteringRate

open scoped NNReal

namespace GaussianFilter

/-- The normalization coefficient at inverse variance is a square
root, including zero variance. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, Gaussian normalization in equation (3.8). -/
theorem kernel_inv_zero_eq_sqrt (s : ℝ≥0) :
    kernel s⁻¹ 0 = Real.sqrt ((s : ℝ) / (2 * Real.pi)) := by
  rw [kernel_eq]
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  rw [NNReal.coe_inv, ← Real.sqrt_inv, mul_inv_rev, inv_inv, div_eq_mul_inv]

end GaussianFilter

namespace GaussianFilter

/-- The explicit frequency-separation bound has a uniform positive
exponential rate. The prefactor is linear in the nonnegative support
parameter, and neither a rate nor a decay estimate is supplied as a
premise. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
Gaussian frequency separation with T=ℓ/(2v). -/
theorem exists_gaussianFrequencyClusteringRate
    (Δ v : ℝ) (hΔ : 0 < Δ) (hv : 0 < v) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ m : ℝ, 0 ≤ m → ∀ ℓ : ℝ, 1 ≤ ℓ →
      2 * Real.exp (-ℓ * Δ / (4 * v)) +
          Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) *
            (2 * m * v * Real.exp (-ℓ / 2) +
              (4 * v / ℓ) * Real.exp (-ℓ * Δ / (4 * v))) ≤
        C * (m + 1) * Real.exp (-κ * ℓ) := by
  let a := Δ / (4 * v)
  let c := Real.sqrt (1 / (4 * Real.pi * v * Δ))
  let κ := min (1 / 4 : ℝ) (Δ / (8 * v))
  let C := 2 + 12 * c * v
  have ha : 0 < a := div_pos hΔ (by positivity)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hκ : 0 < κ := lt_min (by norm_num) (div_pos hΔ (by positivity))
  have hκquarter : κ ≤ 1 / 4 := min_le_left _ _
  have hκa : κ ≤ a := by
    have hhalf : Δ / (8 * v) = a / 2 := by
      dsimp only [a]
      field_simp [hv.ne']
      ring
    exact (min_le_right _ _).trans (by rw [hhalf]; linarith)
  refine ⟨C, κ, hC, hκ, fun m hm ℓ hℓ ↦ ?_⟩
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hsqrt : Real.sqrt ℓ ≤ ℓ := Real.sqrt_le_self_iff.mpr (Or.inr hℓ)
  have hquot : Real.sqrt ℓ / ℓ ≤ 1 := (div_le_one hℓpos).mpr hsqrt
  have hfactor : Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) = c * Real.sqrt ℓ := by
    rw [show ℓ / (4 * Real.pi * v * Δ) =
      ℓ * (1 / (4 * Real.pi * v * Δ)) by ring, Real.sqrt_mul hℓpos.le]
    exact mul_comm _ _
  have htail : Real.exp (-ℓ * Δ / (4 * v)) ≤ Real.exp (-κ * ℓ) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hκa hℓpos.le
    dsimp only [a] at hmul
    calc
      -ℓ * Δ / (4 * v) = -(Δ / (4 * v) * ℓ) := by ring
      _ ≤ -(κ * ℓ) := neg_le_neg hmul
      _ = -κ * ℓ := by ring
  have hquarter : Real.exp (-ℓ / 4) ≤ Real.exp (-κ * ℓ) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hκquarter hℓpos.le]
  have hlinear : ℓ ≤ 4 * Real.exp (ℓ / 4) := by
    have hexp := Real.add_one_le_exp (ℓ / 4)
    linarith
  have hhalf : ℓ * Real.exp (-ℓ / 2) ≤ 4 * Real.exp (-κ * ℓ) := by
    calc
      _ ≤ (4 * Real.exp (ℓ / 4)) * Real.exp (-ℓ / 2) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
      _ = 4 * Real.exp (-ℓ / 4) := by
        rw [mul_assoc, ← Real.exp_add, show ℓ / 4 + -ℓ / 2 = -ℓ / 4 by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left hquarter (by norm_num)
  have hrootHalf : Real.sqrt ℓ * Real.exp (-ℓ / 2) ≤
      4 * Real.exp (-κ * ℓ) :=
    (mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le).trans hhalf
  have hrootTail : (Real.sqrt ℓ / ℓ) * Real.exp (-ℓ * Δ / (4 * v)) ≤
      Real.exp (-κ * ℓ) := by
    exact (mul_le_mul_of_nonneg_right hquot (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using htail)
  rw [hfactor]
  calc
    _ = 2 * Real.exp (-ℓ * Δ / (4 * v)) +
        (2 * c * m * v) * (Real.sqrt ℓ * Real.exp (-ℓ / 2)) +
        (4 * c * v) * ((Real.sqrt ℓ / ℓ) * Real.exp (-ℓ * Δ / (4 * v))) := by ring
    _ ≤ 2 * Real.exp (-κ * ℓ) +
        (2 * c * m * v) * (4 * Real.exp (-κ * ℓ)) +
        (4 * c * v) * Real.exp (-κ * ℓ) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num))
          (mul_le_mul_of_nonneg_left hrootHalf (by positivity)))
        (mul_le_mul_of_nonneg_left hrootTail (by positivity))
    _ = (2 + 8 * c * m * v + 4 * c * v) * Real.exp (-κ * ℓ) := by ring
    _ ≤ C * (m + 1) * Real.exp (-κ * ℓ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      dsimp only [C]
      nlinarith [mul_nonneg hc hv.le, mul_nonneg (mul_nonneg hc hv.le) hm]

end GaussianFilter

end FrequencyClusteringRate
