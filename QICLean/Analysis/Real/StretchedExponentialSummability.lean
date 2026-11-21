/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial moments and tails of stretched exponentials

Every polynomial moment of a stretched exponential with positive rate and positive
exponent is summable. Splitting the rate in half gives an explicit tail bound by
the full half-rate moment times a stretched exponential at the cutoff.

These independently written scalar estimates support the shell sums in the
area-law manuscript, `09-amplification.tex`, lines 141–159 and 187–212, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. They do not construct a spatial kernel
or assert the full amplification theorem.
-/

open Filter
open scoped BigOperators

namespace Real

/-- A stretched exponential has every natural polynomial moment. -/
theorem summable_nat_pow_mul_exp_neg_mul_rpow (p : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ p * exp (-c * (n : ℝ) ^ α)) := by
  have hdecay := (isLittleO_exp_neg_mul_rpow_atTop hc ((-(p : ℝ) - 2) / α)).comp_tendsto
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)
  have hbound : ∀ᶠ n : ℕ in atTop,
      exp (-c * (n : ℝ) ^ α) ≤ (n : ℝ) ^ (-(p : ℝ) - 2) := by
    filter_upwards [hdecay.bound (show (0 : ℝ) < 1 by norm_num)] with n hn
    calc
      exp (-c * (n : ℝ) ^ α) = ‖exp (-c * (n : ℝ) ^ α)‖ :=
        (norm_of_nonneg (exp_pos _).le).symm
      _ ≤ 1 * ‖((n : ℝ) ^ α) ^ ((-(p : ℝ) - 2) / α)‖ := hn
      _ = (n : ℝ) ^ (-(p : ℝ) - 2) := by
        rw [one_mul, norm_of_nonneg (by positivity), ← rpow_mul (by positivity)]
        congr 1
        field_simp
  apply ((summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)).mul_left
    ((2 : ℝ) ^ p)).of_norm_bounded_eventually_nat
  filter_upwards [hbound, eventually_ge_atTop 1] with n hdecay hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := zero_lt_one.trans_le hn₁
  rw [norm_of_nonneg (by positivity)]
  calc
    (1 + (n : ℝ)) ^ p * exp (-c * (n : ℝ) ^ α) ≤
        (2 * (n : ℝ)) ^ p * (n : ℝ) ^ (-(p : ℝ) - 2) := by
      apply mul_le_mul _ hdecay (exp_pos _).le (by positivity)
      gcongr
      linarith
    _ = (2 : ℝ) ^ p * (n : ℝ) ^ (-2 : ℝ) := by
      rw [mul_pow, mul_assoc, ← rpow_natCast (n : ℝ) p, ← rpow_add hn₀]
      congr 2
      ring

/-- The full moment is at least one, from its radius-zero term. -/
theorem one_le_tsum_nat_pow_mul_exp_neg_mul_rpow (p : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    1 ≤ ∑' n : ℕ, (1 + (n : ℝ)) ^ p * exp (-c * (n : ℝ) ^ α) := by
  simpa [zero_rpow hα.ne'] using
    (summable_nat_pow_mul_exp_neg_mul_rpow p hc hα).le_tsum 0 (fun _ _ => by positivity)

/-- The tail beyond a nonnegative real cutoff is bounded by the full half-rate
moment times the half-rate stretched exponential at that cutoff. -/
theorem tsum_nat_pow_mul_exp_neg_mul_rpow_tail_le (p : ℕ) {c α r : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hr : 0 ≤ r) :
    (∑' n : {n : ℕ // r ≤ (n : ℝ)},
      (1 + (n.val : ℝ)) ^ p * exp (-c * (n.val : ℝ) ^ α)) ≤
      (∑' n : ℕ, (1 + (n : ℝ)) ^ p * exp (-(c / 2) * (n : ℝ) ^ α)) *
        exp (-(c / 2) * r ^ α) := by
  have hfull := summable_nat_pow_mul_exp_neg_mul_rpow p hc hα
  have hhalf := summable_nat_pow_mul_exp_neg_mul_rpow p (half_pos hc) hα
  calc
    (∑' n : {n : ℕ // r ≤ (n : ℝ)},
        (1 + (n.val : ℝ)) ^ p * exp (-c * (n.val : ℝ) ^ α)) ≤
        ∑' n : ℕ, (1 + (n : ℝ)) ^ p * exp (-(c / 2) * (n : ℝ) ^ α) *
          exp (-(c / 2) * r ^ α) := by
      refine Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => by positivity) (fun n => ?_) (hfull.subtype _) (hhalf.mul_right _)
      have hrn := rpow_le_rpow hr n.property hα.le
      calc
        (1 + (n.val : ℝ)) ^ p * exp (-c * (n.val : ℝ) ^ α) =
            ((1 + (n.val : ℝ)) ^ p * exp (-(c / 2) * (n.val : ℝ) ^ α)) *
              exp (-(c / 2) * (n.val : ℝ) ^ α) := by
          rw [mul_assoc, ← exp_add]
          congr 2
          ring
        _ ≤ (1 + (n.val : ℝ)) ^ p * exp (-(c / 2) * (n.val : ℝ) ^ α) *
            exp (-(c / 2) * r ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hrn (by linarith)
    _ = _ := tsum_mul_right

end Real
