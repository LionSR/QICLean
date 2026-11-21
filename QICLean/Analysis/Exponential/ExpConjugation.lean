/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Analysis.Exponential.MatrixCommutator
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Algebra.Group.IsApply
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Conjugation by a matrix exponential

Write `ad_H(X) = HX - XH`. If `‖ad_H^m O‖ ≤ R (R + a) ⋯ (R + (m - 1) a) ‖O‖` for every `m`,
with `a > 0`, then the Hadamard series `e^{sH} O e^{-sH} = ∑ₘ sᵐ/m! · ad_H^m O` is majorized
by the binomial series of `(1 - as)^{-R/a}`, so `‖e^{sH} O e^{-sH}‖ ≤ ‖O‖ (1 - as)^{-R/a}` for
`0 ≤ s < 1/a`. The factorial growth `‖ad_H^m O‖ ≤ a^m m! ‖O‖` is the case `R = a`, and gives
`‖e^{sH} O e^{-sH}‖ ≤ 2‖O‖` for `0 ≤ s` with `as ≤ 1/2`. No locality or Hermiticity is
assumed; locality enters only through the growth bound. A positive matrix `h ≥ 0` satisfies
`‖hO - Oh‖ ≤ ‖h‖ ‖O‖`, since `h - ‖h‖/2` has norm at most `‖h‖/2`.

Moved from TNLean, `TNLean/Algebra/ExpConjugation.lean` at commit
`e41c3b63`; the growth rate is no longer assumed nonnegative, since the growth bound at
`m = 1` forces it unless `O = 0`. The binomial form, and the commutator bound for every
positive `h` instead of a positive contraction, are added here.

## Main results

* `Matrix.norm_exp_conjugation_le_of_growth` — the conjugation bound `(1 - as)^{-R/a}` from
  the growth `∏_{j < m} (R + j a)`.
* `Matrix.norm_exp_conjugation_le_two_of_growth` — the conjugation bound from factorial growth.
* `Matrix.norm_commutator_le_of_nonneg` — commutators with a positive matrix.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 804–877 (the Hadamard expansion, the commutator estimate for a
  positive term, and the binomial series).
-/

open scoped Matrix.Norms.L2Operator BigOperators

namespace ContinuousLinearMap

/-- The exponential series of `s T`, evaluated at a vector. -/
private theorem hasSum_exp_smul_apply_pow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (s : ℂ) (O : E) :
    HasSum (fun m : ℕ ↦ (s ^ m / (m.factorial : ℂ)) • (T ^ m) O)
      ((NormedSpace.exp (s • T)) O) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • T)).mapL
    (ContinuousLinearMap.apply ℂ E O)
  simpa only [ContinuousLinearMap.apply_apply, smul_pow, smul_apply, smul_smul, div_eq_mul_inv,
    mul_comm] using h

end ContinuousLinearMap

namespace Real

/-- The ascending product `r (r + 1) ⋯ (r + m - 1)` divided by `m!` is the binomial coefficient
`(r + m - 1 choose m)`. -/
private theorem choose_add_sub_one_eq (r : ℝ) (m : ℕ) :
    Ring.choose (r + m - 1) m = (∏ j ∈ Finset.range m, (r + j)) / m.factorial := by
  have hasc : (ascPochhammer ℝ m).eval r = ∏ j ∈ Finset.range m, (r + j) := by
    induction m with
    | zero => simp
    | succ m ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    show r + m - 1 - m + 1 = r by ring, Polynomial.ascPochhammer_smeval_eq_eval, hasc,
    smul_eq_mul, div_eq_inv_mul]

/-- **The binomial series of `(1 - x)^{-r}`.** For `|x| < 1`,
`∑ₘ r (r + 1) ⋯ (r + m - 1) xᵐ / m! = (1 - x)^{-r}`. AKL14, arXiv:1406.3898, proof of
`lem:Hadamard-bound`, `low70.tex`, lines 869–877. -/
private theorem hasSum_prod_range_div_factorial_mul_pow (r : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ ↦ (∏ j ∈ Finset.range m, (r + j)) / m.factorial * x ^ m)
      ((1 - x) ^ (-r)) := by
  have h := (one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum (y := x)
    (by simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ← NNReal.coe_lt_coe]
      using hx)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at h
  rw [rpow_neg (by linarith [(abs_lt.mp hx).2]), ← one_div]
  simpa only [choose_add_sub_one_eq] using h

end Real

namespace Matrix

/-- **Conjugation from binomial commutator growth.** Let `0 < a`. If
`‖ad_H^m O‖ ≤ R (R + a) ⋯ (R + (m - 1) a) ‖O‖` for every `m`, then
`‖e^{sH} O e^{-sH}‖ ≤ ‖O‖ (1 - as)^{-R/a}` for `0 ≤ s` with `as < 1`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 804–877, with
`a = gk`. -/
theorem norm_exp_conjugation_le_of_growth {n : Type*} [Fintype n] [DecidableEq n]
    (H O : Matrix n n ℂ) {a R s : ℝ} (ha : 0 < a) (hs0 : 0 ≤ s) (hs : a * s < 1)
    (hgrowth : ∀ m : ℕ,
      ‖(GaussianFilter.commutatorCLM H ^ m) O‖ ≤ (∏ j ∈ Finset.range m, (R + j * a)) * ‖O‖) :
    ‖NormedSpace.exp ((s : ℂ) • H) * O * NormedSpace.exp (-((s : ℂ) • H))‖ ≤
      ‖O‖ * (1 - a * s) ^ (-(R / a)) := by
  have hsum := ContinuousLinearMap.hasSum_exp_smul_apply_pow
    (GaussianFilter.commutatorCLM H) (s : ℂ) O
  have hbin := (Real.hasSum_prod_range_div_factorial_mul_pow (R / a)
    (x := a * s) (by rw [abs_lt]; constructor <;> nlinarith)).mul_left ‖O‖
  have hprod (m : ℕ) : ∏ j ∈ Finset.range m, (R + j * a) =
      a ^ m * ∏ j ∈ Finset.range m, (R / a + j) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ,
        show R + m * a = a * (R / a + m) by rw [mul_add, mul_div_cancel₀ _ ha.ne']; ring]
      ring
  have hbound (m : ℕ) :
      ‖((s : ℂ) ^ m / (m.factorial : ℂ)) • (GaussianFilter.commutatorCLM H ^ m) O‖ ≤
        ‖O‖ * ((∏ j ∈ Finset.range m, (R / a + j)) / m.factorial * (a * s) ^ m) := by
    have hfac : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    rw [norm_smul, norm_div, norm_pow, Complex.norm_of_nonneg hs0, Complex.norm_natCast]
    calc
      _ ≤ (s ^ m / (m.factorial : ℝ)) * ((∏ j ∈ Finset.range m, (R + j * a)) * ‖O‖) :=
        mul_le_mul_of_nonneg_left (hgrowth m) (div_nonneg (pow_nonneg hs0 _) hfac.le)
      _ = _ := by rw [hprod, mul_pow]; ring
  have h := tsum_of_norm_bounded hbin hbound
  rwa [hsum.tsum_eq, GaussianFilter.exp_smul_commutatorCLM_apply] at h

/-- **Conjugation from factorial commutator growth.** If `‖ad_H^m O‖ ≤ a^m m! ‖O‖` for every
`m`, then `‖e^{sH} O e^{-sH}‖ ≤ 2‖O‖` for `0 ≤ s` with `as ≤ 1/2`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 804–877: the case
`R = gk` of `norm_exp_conjugation_le_of_growth`, where `(1 - gks)^{-1} ≤ 2`. -/
theorem norm_exp_conjugation_le_two_of_growth {n : Type*} [Fintype n] [DecidableEq n]
    (H O : Matrix n n ℂ) (a s : ℝ)
    (hs0 : 0 ≤ s) (hs : a * s ≤ 1 / 2)
    (hgrowth : ∀ m : ℕ,
      ‖(GaussianFilter.commutatorCLM H ^ m) O‖ ≤ a ^ m * (m.factorial : ℝ) * ‖O‖) :
    ‖NormedSpace.exp ((s : ℂ) • H) * O *
      NormedSpace.exp (-((s : ℂ) • H))‖ ≤ 2 * ‖O‖ := by
  rcases eq_or_ne O 0 with rfl | hO
  · simp
  rcases hs0.eq_or_lt with rfl | hs0'
  · simp only [Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul, mul_one]
    linarith [norm_nonneg O]
  have ha : 0 ≤ a := by
    have h1 := hgrowth 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h1
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) (norm_pos_iff.mpr hO)
  -- Compare with the growth rate `b = 1/(2s) ≥ a`, at which `bs = 1/2`.
  set b := 1 / (2 * s)
  have hb : 0 < b := by positivity
  have hbs : b * s = 1 / 2 := by
    rw [show b = 1 / (2 * s) from rfl]
    field_simp
  have hab : a ≤ b := by rw [le_div_iff₀ (by positivity)]; linarith
  have h := norm_exp_conjugation_le_of_growth H O (R := b) hb hs0 (by linarith) fun m ↦ by
    refine (hgrowth m).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg O))
    have hprod : ∏ j ∈ Finset.range m, (b + j * b) = b ^ m * m.factorial := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, ih, pow_succ, Nat.factorial_succ]
        push_cast
        ring
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab m) (Nat.cast_nonneg _)
  rw [hbs, div_self hb.ne', show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.rpow_neg_one,
    inv_inv] at h
  linarith

open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `0 ≤ h`, then `‖hO - Oh‖ ≤ ‖h‖ ‖O‖` for every `O`: the matrix `h - ‖h‖/2` has norm at
most `‖h‖/2`. AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`,
lines 831–837. -/
theorem norm_commutator_le_of_nonneg (h O : Matrix n n ℂ) (h0 : 0 ≤ h) :
    ‖h * O - O * h‖ ≤ ‖h‖ * ‖O‖ := by
  let c : Matrix n n ℂ := (‖h‖ / 2 : ℝ) • 1
  have hsplit : (‖h‖ : ℝ) • (1 : Matrix n n ℂ) = c + c := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hlo : -c ≤ h - c := by
    simpa only [zero_sub] using sub_le_sub_right h0 c
  have hhi : h - c ≤ c := by
    apply (sub_le_iff_le_add).2
    rw [← hsplit, ← Algebra.algebraMap_eq_smul_one]
    exact IsSelfAdjoint.le_algebraMap_norm_self h (IsSelfAdjoint.of_nonneg h0)
  have hcself : IsSelfAdjoint c :=
    IsSelfAdjoint.smul (IsSelfAdjoint.all (‖h‖ / 2 : ℝ)) (IsSelfAdjoint.one (Matrix n n ℂ))
  have hcenterself : IsSelfAdjoint (h - c) := (IsSelfAdjoint.of_nonneg h0).sub hcself
  have hnorm1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one (Matrix n n ℂ))
  have hcnorm : ‖c‖ ≤ ‖h‖ / 2 := by
    calc
      ‖c‖ = ‖h‖ / 2 * ‖(1 : Matrix n n ℂ)‖ := by
        dsimp [c]
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ‖h‖ / 2 * 1 := mul_le_mul_of_nonneg_left hnorm1 (by positivity)
      _ = ‖h‖ / 2 := mul_one _
  have hcenternorm : ‖h - c‖ ≤ ‖h‖ / 2 := by
    refine le_trans ?_ hcnorm
    simpa only [norm_neg, max_self] using
      (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hcenterself)
  have hcomm : h * O - O * h = (h - c) * O - O * (h - c) := by
    dsimp [c]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  calc
    ‖h * O - O * h‖ = ‖(h - c) * O - O * (h - c)‖ := congrArg (‖·‖) hcomm
    _ ≤ ‖(h - c) * O‖ + ‖O * (h - c)‖ := norm_sub_le _ _
    _ ≤ ‖h - c‖ * ‖O‖ + ‖O‖ * ‖h - c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖h‖ / 2 * ‖O‖ + ‖O‖ * (‖h‖ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hcenternorm (norm_nonneg O))
        (mul_le_mul_of_nonneg_left hcenternorm (norm_nonneg O))
    _ = ‖h‖ * ‖O‖ := by ring

end Matrix

section CommutingExponentialOrder

/-!
# Exponential order for commuting Hermitian matrices

The exponential preserves order between commuting Hermitian matrices. The proof
writes their positive difference as `D` and uses `exp(D) ≥ 1`, together with
`exp(B)-exp(A)=exp(A)(exp(D)-1)`. Positivity of this last product follows from
commutation.

This is the scalar functional-calculus comparison used for the whole and grouped
copy labels in OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 455--476,
`comparator:restriction-dimensions` and `comparator:whole-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponentiating an order comparison is valid for commuting Hermitian matrices.
Source: the common-label comparison in `07-comparators.tex`, lines 455--476. -/
theorem IsHermitian.exp_le_exp_of_commute {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (h : A ≤ B) :
    NormedSpace.exp A ≤ NormedSpace.exp B := by
  have hD : IsSelfAdjoint (B - A) := (hB.sub hA).isSelfAdjoint
  have hDnonneg : 0 ≤ B - A := sub_nonneg.mpr h
  have hOne : 1 ≤ NormedSpace.exp (B - A) := by
    rw [← CFC.real_exp_eq_normedSpace_exp hD]
    exact one_le_cfc Real.exp (B - A)
      (fun x hx => Real.one_le_exp (spectrum_nonneg_of_nonneg hDnonneg hx))
      (ha := hD)
  have hAD : Commute A (B - A) := hAB.sub_right (Commute.refl A)
  have hprod : 0 ≤ NormedSpace.exp A * (NormedSpace.exp (B - A) - 1) :=
    Commute.mul_nonneg hA.isSelfAdjoint.exp_nonneg (sub_nonneg.mpr hOne)
      (hAD.exp.sub_right (Commute.one_right _))
  rw [mul_sub, mul_one, ← Matrix.exp_add_of_commute _ _ hAD,
    show A + (B - A) = B by abel] at hprod
  exact sub_nonneg.mp hprod

end Matrix

end CommutingExponentialOrder
