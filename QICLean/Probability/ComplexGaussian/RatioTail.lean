/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The lower tail of a complex Gaussian coordinate ratio

Let `g_1, …, g_q` be independent standard circular complex Gaussians, normalized by
`E |g_i|² = 1`, and let `A` be a set of `s` of the indices. The fraction of the total squared
norm `∑_i |g_i|²` carried by the coordinates in `A` has mean `s / q`. This file proves that it
falls below half its mean with probability at most `exp (-s / 16)`:

  `P (∑_{i ∈ A} |g_i|² ≤ (s / (2 q)) ∑_i |g_i|²) ≤ exp (-s / 16)`.

This is the concentration step in the random sampling lemma of Arad, Landau, Vazirani and
Vidick, *Rigorous RG algorithms and area laws for low energy eigenstates in 1D*
(arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Lemma `l:rs`, lines 531–547). The source cites
Dasgupta and Gupta, *An elementary proof of a theorem of Johnson and Lindenstrauss*,
Theorem 2.1, for the probability `e^{-s/16}` of the event `‖P_{W'} w‖² < (s / (2 q)) ‖w‖²`.
Dasgupta and Gupta work with real Gaussian vectors; their lower-tail estimate at half the mean
is `exp (-(s / 2) (log 2 - 1 / 2))`. A complex coordinate is a pair of real ones, so in the
complex case `2 s` of `2 q` real coordinates are selected and the exponent only improves. The
proof below is a direct Chernoff bound for the complex coordinates with the fixed parameter
`1 / 2`, which gives exactly the source's `e^{-s/16}`.

## Main results

* `integral_exp_sum_mul_norm_coordinate_sq`: for weights `c i < 1`,
  `E exp (∑_i c_i |g_i|²) = ∏_i (1 - c_i)⁻¹`.
* `integral_exp_mul_norm_coordinate_sq`: the single-coordinate case
  `E exp (c |g_i|²) = (1 - c)⁻¹` for `c < 1`.
* `measureReal_sum_norm_coordinate_sq_le_le`: the lower-tail bound above.

## Proof

The event is `Z ≤ 0` for `Z = ∑_i w_i |g_i|²`, with `w_i = 1 - a` on `A`, `w_i = -a` off `A`
and `a = s / (2 q)`. Markov's inequality for `exp (-Z / 2)` bounds its probability by
`∏_i (1 + w_i / 2)⁻¹`, computed from the real Gaussian integral and the product structure of
the standard Gaussian measure. Each factor `u = (1 + w_i / 2)⁻¹` satisfies `u ≤ exp (u - 1)`,
and the resulting exponent is at most `-s / 16` by a polynomial inequality valid for `s ≤ q`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace QICLean.ComplexGaussian

noncomputable section

/-- The moment generating function of the square of a standard real Gaussian:
`E exp (b t²) = (√(1 - 2 b))⁻¹` for `b < 1 / 2`. -/
theorem integral_exp_mul_sq_gaussianReal {b : ℝ} (hb : b < 1 / 2) :
    (∫ t, rexp (b * t ^ 2) ∂gaussianReal 0 1) = (√(1 - 2 * b))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have he (t : ℝ) : gaussianPDFReal 0 1 t • rexp (b * t ^ 2) =
      (√(2 * π))⁻¹ * rexp (-(1 / 2 - b) * t ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  simp_rw [he, integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * b := by linarith
  have h2 : π / (1 / 2 - b) = (2 * π) / (1 - 2 * b) := by
    field_simp
  rw [h2, Real.sqrt_div' _ h1.le, div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- The function `exp (b t²)` is integrable against the standard real Gaussian for
`b < 1 / 2`. -/
theorem integrable_exp_mul_sq_gaussianReal {b : ℝ} (hb : b < 1 / 2) :
    Integrable (fun t ↦ rexp (b * t ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  have he : (fun t : ℝ ↦ (gaussianPDF 0 1 t).toReal • rexp (b * t ^ 2)) =
      fun t ↦ (√(2 * π))⁻¹ * rexp (-(1 / 2 - b) * t ^ 2) := by
    funext t
    simp only [toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
      smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  exact (integrable_exp_neg_mul_sq (by linarith)).const_mul _

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- The squared modulus of a circular complex coordinate is half the sum of the squares of its
two real coordinates. -/
theorem norm_coordinate_sq (i : ι) (x : Sample ι) :
    ‖coordinate i x‖ ^ 2 = (x (i, 0) ^ 2 + x (i, 1) ^ 2) / 2 := by
  rw [coordinate_apply, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt zero_le_two, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

/-- The integrand of the moment generating function, written on the real coordinates. -/
private theorem exp_sum_mul_norm_coordinate_sq (c : ι → ℝ) (y : ι × Fin 2 → ℝ) :
    rexp (∑ i, c i * ‖coordinate i (WithLp.toLp 2 y)‖ ^ 2) =
      ∏ p : ι × Fin 2, rexp (c p.1 / 2 * y p ^ 2) := by
  rw [← Real.exp_sum, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [norm_coordinate_sq, Fin.sum_univ_two]
  ring

private theorem measurable_exp_sum_mul_norm_coordinate_sq (c : ι → ℝ) :
    Measurable fun x : Sample ι ↦ rexp (∑ i, c i * ‖coordinate i x‖ ^ 2) := by
  simp_rw [norm_coordinate_sq]
  fun_prop

/-- The exponential moments of the squared moduli are integrable below the threshold. -/
theorem integrable_exp_sum_mul_norm_coordinate_sq (c : ι → ℝ) (hc : ∀ i, c i < 1) :
    Integrable (fun x ↦ rexp (∑ i, c i * ‖coordinate i x‖ ^ 2)) (law ι) := by
  rw [law, ← map_pi_eq_stdGaussian, integrable_map_measure
    (measurable_exp_sum_mul_norm_coordinate_sq c).aestronglyMeasurable (by fun_prop)]
  simp only [Function.comp_def, exp_sum_mul_norm_coordinate_sq]
  exact Integrable.fintype_prod fun p ↦
    integrable_exp_mul_sq_gaussianReal (by linarith [hc p.1])

/-- The joint moment generating function of the squared moduli of independent standard circular
complex Gaussians: `E exp (∑_i c_i |g_i|²) = ∏_i (1 - c_i)⁻¹` for weights `c_i < 1`. -/
theorem integral_exp_sum_mul_norm_coordinate_sq (c : ι → ℝ) (hc : ∀ i, c i < 1) :
    (∫ x, rexp (∑ i, c i * ‖coordinate i x‖ ^ 2) ∂law ι) = ∏ i, (1 - c i)⁻¹ := by
  rw [law, ← map_pi_eq_stdGaussian, integral_map (by fun_prop)
    (measurable_exp_sum_mul_norm_coordinate_sq c).aestronglyMeasurable]
  simp only [exp_sum_mul_norm_coordinate_sq]
  rw [integral_fintype_prod_eq_prod (ι := ι × Fin 2) (fun p (t : ℝ) ↦ rexp (c p.1 / 2 * t ^ 2)),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h : c i / 2 < 1 / 2 := by linarith [hc i]
  rw [Fin.prod_univ_two, integral_exp_mul_sq_gaussianReal h, ← mul_inv, ← pow_two,
    Real.sq_sqrt (by linarith [hc i])]
  ring_nf

/-- The moment generating function of the squared modulus of a standard circular complex
Gaussian: `E exp (c |g_i|²) = (1 - c)⁻¹` for `c < 1`. -/
theorem integral_exp_mul_norm_coordinate_sq (i : ι) {c : ℝ} (hc : c < 1) :
    (∫ x, rexp (c * ‖coordinate i x‖ ^ 2) ∂law ι) = (1 - c)⁻¹ := by
  classical
  have h := integral_exp_sum_mul_norm_coordinate_sq (Pi.single i c : ι → ℝ) fun j ↦ by
    by_cases hj : j = i
    · subst hj; simpa using hc
    · simp [hj]
  have hs (x : Sample ι) : ∑ j, (Pi.single i c : ι → ℝ) j * ‖coordinate j x‖ ^ 2 =
      c * ‖coordinate i x‖ ^ 2 := by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp
  simp_rw [hs] at h
  rw [h, Finset.prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

/-- The exponent bound behind `exp (-s / 16)`: for `0 ≤ s ≤ q` and `a = s / (2 q)`,
`s ((1 + (1 - a) / 2)⁻¹ - 1) + (q - s) ((1 - a / 2)⁻¹ - 1) ≤ -s / 16`. -/
private theorem ratioTail_exponent_le {s q : ℝ} (hs : 0 ≤ s) (hsq : s ≤ q) :
    s * ((1 + (1 - s / (2 * q)) / 2)⁻¹ - 1) + (q - s) * ((1 - s / (2 * q) / 2)⁻¹ - 1) ≤
      -(s / 16) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  have hq : 0 < q := hs.trans_le hsq
  have h6 : 0 < 6 * q - s := by linarith
  have h4 : 0 < 4 * q - s := by linarith
  have h1 : (1 + (1 - s / (2 * q)) / 2)⁻¹ - 1 = -(2 * q - s) / (6 * q - s) := by
    rw [show 1 + (1 - s / (2 * q)) / 2 = (6 * q - s) / (4 * q) by field_simp; ring, inv_div,
      eq_div_iff h6.ne', sub_mul, div_mul_cancel₀ _ h6.ne']
    ring
  have h2 : (1 - s / (2 * q) / 2)⁻¹ - 1 = s / (4 * q - s) := by
    rw [show 1 - s / (2 * q) / 2 = (4 * q - s) / (4 * q) by field_simp; ring, inv_div,
      eq_div_iff h4.ne', sub_mul, div_mul_cancel₀ _ h4.ne']
    ring
  rw [h1, h2, mul_div_assoc', mul_div_assoc', div_add_div _ _ h6.ne' h4.ne',
    div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hs hq, mul_pos (mul_pos hs hq) hq, mul_nonneg hs.le (sub_nonneg.2 hsq),
    mul_nonneg (mul_nonneg hs.le hs.le) (sub_nonneg.2 hsq)]

/-- **Lower tail of a complex Gaussian coordinate ratio.** For independent standard circular
complex Gaussians `g_i` indexed by a set of size `q` and a subset `A` of size `s`,
`P (∑_{i ∈ A} |g_i|² ≤ (s / (2 q)) ∑_i |g_i|²) ≤ exp (-s / 16)`.

This is the concentration step of Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, Lemma `l:rs`
(`local_alg_arxiv_v2.tex`, lines 531–547), citing Dasgupta–Gupta, Theorem 2.1. -/
theorem measureReal_sum_norm_coordinate_sq_le_le (A : Finset ι) :
    (law ι).real {x | ∑ i ∈ A, ‖coordinate i x‖ ^ 2 ≤
      (A.card / (2 * Fintype.card ι)) * ∑ i, ‖coordinate i x‖ ^ 2} ≤
      rexp (-(A.card / 16)) := by
  classical
  set s : ℝ := (A.card : ℝ)
  set q : ℝ := (Fintype.card ι : ℝ)
  set a : ℝ := s / (2 * q)
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hsq : s ≤ q := by
    simp only [s, q]
    exact_mod_cast A.card_le_univ
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ 1 / 2 := by
    rcases hs0.eq_or_lt with h | h
    · simp [a, ← h]
    · rw [div_le_iff₀ (by linarith)]
      linarith
  let w : ι → ℝ := fun i ↦ (if i ∈ A then 1 else 0) - a
  let Z : Sample ι → ℝ := fun x ↦ ∑ i, w i * ‖coordinate i x‖ ^ 2
  have hset : {x | ∑ i ∈ A, ‖coordinate i x‖ ^ 2 ≤ a * ∑ i, ‖coordinate i x‖ ^ 2} =
      {x | Z x ≤ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Z, w, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, sub_nonpos]
  have hc : ∀ i, -1 / 2 * w i < 1 := fun i ↦ by
    simp only [w]
    split_ifs <;> linarith
  have hZ (x : Sample ι) : -1 / 2 * Z x = ∑ i, -1 / 2 * w i * ‖coordinate i x‖ ^ 2 := by
    simp only [Z, Finset.mul_sum, mul_assoc]
  have hint : Integrable (fun x ↦ rexp (-1 / 2 * Z x)) (law ι) := by
    simp_rw [hZ]
    exact integrable_exp_sum_mul_norm_coordinate_sq _ hc
  have hmgf : mgf Z (law ι) (-1 / 2) = ∏ i, (1 - -1 / 2 * w i)⁻¹ := by
    rw [mgf]
    simp_rw [hZ]
    exact integral_exp_sum_mul_norm_coordinate_sq _ hc
  have hpos : ∀ i, 0 < 1 - -1 / 2 * w i := fun i ↦ by linarith [hc i]
  calc (law ι).real {x | ∑ i ∈ A, ‖coordinate i x‖ ^ 2 ≤ a * ∑ i, ‖coordinate i x‖ ^ 2}
      = (law ι).real {x | Z x ≤ 0} := by rw [hset]
    _ ≤ rexp (-(-1 / 2) * 0) * mgf Z (law ι) (-1 / 2) :=
      measure_le_le_exp_mul_mgf 0 (by norm_num) hint
    _ = ∏ i, (1 - -1 / 2 * w i)⁻¹ := by rw [hmgf]; simp
    _ ≤ ∏ i, rexp ((1 - -1 / 2 * w i)⁻¹ - 1) :=
      Finset.prod_le_prod₀ (fun i _ ↦ (inv_pos.2 (hpos i)).le) fun i _ ↦ by
        linarith [Real.add_one_le_exp ((1 - -1 / 2 * w i)⁻¹ - 1)]
    _ = rexp (s * ((1 + (1 - a) / 2)⁻¹ - 1) + (q - s) * ((1 - a / 2)⁻¹ - 1)) := by
      rw [← Real.exp_sum]
      congr 1
      have he (i : ι) : (1 - -1 / 2 * w i)⁻¹ - 1 = ((1 - a / 2)⁻¹ - 1) +
          (if i ∈ A then ((1 + (1 - a) / 2)⁻¹ - 1) - ((1 - a / 2)⁻¹ - 1) else 0) := by
        simp only [w]
        split_ifs <;> ring_nf
      simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_ite_mem, Finset.univ_inter]
      ring
    _ ≤ rexp (-(s / 16)) := Real.exp_le_exp.2 (ratioTail_exponent_le hs0 hsq)

/-- The lower-tail bound `measureReal_sum_norm_coordinate_sq_le_le` stated for the measure. -/
theorem measure_sum_norm_coordinate_sq_le_le (A : Finset ι) :
    law ι {x | ∑ i ∈ A, ‖coordinate i x‖ ^ 2 ≤
      (A.card / (2 * Fintype.card ι)) * ∑ i, ‖coordinate i x‖ ^ 2} ≤
      ENNReal.ofReal (rexp (-(A.card / 16))) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_sum_norm_coordinate_sq_le_le A)

end Coordinates

end

end QICLean.ComplexGaussian
