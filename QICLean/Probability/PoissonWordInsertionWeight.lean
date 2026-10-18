/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWord
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Time-integrated weights for insertion into Poissonized words

Integrating the mass of a prefix of length `m` and a suffix of length `n`
over the insertion time gives the mass of one word of length `m + n + 1`.
The statements include time zero and an empty alphabet. They concern finite
word weights and do not assert a construction from independent clocks.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Nat

namespace PoissonWord

private lemma integral_pow_mul_sub_pow (T : ℝ≥0) (m n : ℕ) :
    (∫ s : ℝ in 0..(T : ℝ), s ^ m * ((T : ℝ) - s) ^ n) =
      (T : ℝ) ^ (m + n + 1) * (m ! : ℝ) * (n ! : ℝ) / ((m + n + 1)! : ℝ) := by
  by_cases hT : T = 0
  · simp [hT]
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
  have hΓ := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (m : ℂ) + 1) (t := (n : ℂ) + 1)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
  have hadd : ((m : ℂ) + 1) + ((n : ℂ) + 1) = (m + n + 1 : ℕ) + 1 := by
    push_cast
    ring
  rw [Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial, hadd,
    Complex.Gamma_nat_eq_factorial] at hΓ
  have hb : Complex.betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1) =
      (m ! : ℂ) * (n ! : ℂ) / ((m + n + 1)! : ℂ) := by
    apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (m + n + 1))).2
    simpa only [mul_comm] using hΓ.symm
  have he : ((m : ℂ) + 1) + ((n : ℂ) + 1) - 1 = (m + n + 1 : ℕ) := by
    push_cast
    ring
  have hs := Complex.betaIntegral_scaled ((m : ℂ) + 1) ((n : ℂ) + 1) hTpos
  rw [he, hb] at hs
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at hs
  apply Complex.ofReal_injective
  push_cast
  rw [← intervalIntegral.integral_ofReal]
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, mul_div_assoc,
    mul_assoc] using hs

variable {ι : Type*} [Fintype ι]

/-- A singleton word mass is continuous as a function of clipped real time. -/
lemma continuous_weight_ofReal (m : ℕ) :
    Continuous (fun s : ℝ ↦ weight ι (Real.toNNReal s) m) := by
  unfold weight
  fun_prop

/-- Insertion-time word masses are measurable. -/
lemma measurable_weight_ofReal (m : ℕ) :
    Measurable (fun s : ℝ ↦ weight ι (Real.toNNReal s) m) :=
  (continuous_weight_ofReal m).measurable

/-- The product of prefix and suffix masses is nonnegative for every real time. -/
lemma weight_mul_weight_nonneg (T : ℝ≥0) (m n : ℕ) (s : ℝ) :
    0 ≤ weight ι (Real.toNNReal s) m * weight ι (Real.toNNReal ((T : ℝ) - s)) n :=
  mul_nonneg (weight_nonneg _ _) (weight_nonneg _ _)

/-- The prefix/suffix mass product is integrable over the insertion interval. -/
lemma intervalIntegrable_weight_mul_weight (T : ℝ≥0) (m n : ℕ) :
    IntervalIntegrable (fun s : ℝ ↦
      weight ι (Real.toNNReal s) m * weight ι (Real.toNNReal ((T : ℝ) - s)) n)
      volume 0 (T : ℝ) :=
  ((continuous_weight_ofReal m).mul
    ((continuous_weight_ofReal n).comp (continuous_const.sub continuous_id))).intervalIntegrable _ _

/-- Integration over the insertion time produces exactly one longer word's mass. -/
theorem integral_weight_mul_weight (T : ℝ≥0) (m n : ℕ) :
    (∫ s : ℝ in 0..(T : ℝ),
      weight ι (Real.toNNReal s) m * weight ι (Real.toNNReal ((T : ℝ) - s)) n) =
      weight ι T (m + n + 1) := by
  have hfactor (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      weight ι (Real.toNNReal s) m * weight ι (Real.toNNReal ((T : ℝ) - s)) n =
        (Real.exp (-(Fintype.card ι : ℝ) * T) / ((m ! : ℝ) * (n ! : ℝ))) *
          (s ^ m * ((T : ℝ) - s) ^ n) := by
    unfold weight
    rw [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    have hexp : Real.exp (-(Fintype.card ι : ℝ) * s) *
        Real.exp (-(Fintype.card ι : ℝ) * ((T : ℝ) - s)) =
        Real.exp (-(Fintype.card ι : ℝ) * T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (-(Fintype.card ι : ℝ) * s) *
          Real.exp (-(Fintype.card ι : ℝ) * ((T : ℝ) - s))) /
          ((m ! : ℝ) * (n ! : ℝ)) * (s ^ m * ((T : ℝ) - s) ^ n) := by ring
      _ = _ := by rw [hexp]
  calc
    _ = ∫ s : ℝ in 0..(T : ℝ),
        (Real.exp (-(Fintype.card ι : ℝ) * T) / ((m ! : ℝ) * (n ! : ℝ))) *
          (s ^ m * ((T : ℝ) - s) ^ n) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le T.coe_nonneg] at hs
      exact hfactor s hs
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow_mul_sub_pow, weight]
      have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp

/-- The nonnegative-integral form of the insertion-time mass identity. -/
theorem lintegral_weight_mul_weight (T : ℝ≥0) (m n : ℕ) :
    (∫⁻ s : ℝ in Ioc 0 (T : ℝ),
      ENNReal.ofReal (weight ι (Real.toNNReal s) m) *
        ENNReal.ofReal (weight ι (Real.toNNReal ((T : ℝ) - s)) n)) =
      ENNReal.ofReal (weight ι T (m + n + 1)) := by
  simp_rw [← ENNReal.ofReal_mul (weight_nonneg _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).1
      (intervalIntegrable_weight_mul_weight T m n))
    (Filter.Eventually.of_forall (weight_mul_weight_nonneg T m n))]
  rw [← intervalIntegral.integral_of_le T.coe_nonneg, integral_weight_mul_weight]

end PoissonWord
