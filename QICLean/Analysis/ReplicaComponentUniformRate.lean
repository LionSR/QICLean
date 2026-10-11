/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ExcitationSubsetCounts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform rates over excitation subsets

The three binomial corrections in the component inverse estimate are
bounded by binary entropy. The number of good copies is at least
`(1 - τ) * k`, so a nonnegative physical entropy difference retains that
fraction of its contribution. A fixed polynomial moment loss is absorbed
into the original polynomial prefactor. All errors remain explicit.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–590, `comparator:component-inverse`
and `comparator:inverse-compression`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- The exact component factors give a rate uniform in every excitation
count `r ≤ τ k`. The original two label logarithms enter through their
sum `L`; the dimensions enter through `d`. No asymptotic error is hidden.
Source: `07-comparators.tex`, lines 550–590. -/
theorem replica_component_prefactor_le_uniform
    {k r : ℕ} (hrk : r ≤ k) {τ a d g K Λ : ℝ}
    (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hr : (r : ℝ) ≤ τ * k)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hg : 0 ≤ g) (hK : 0 ≤ K) (hΛ : 0 ≤ Λ)
    (C S ε L : ℝ) (hL : 2 * (k : ℝ) * S - ε ≤ L) :
    ((k : ℝ) + 2) ^ C * (k.choose r : ℝ) ^ a *
        exp (-a * (L - (r : ℝ) * d - 2 * log (k.choose r : ℝ))) *
        exp (-((k - r : ℕ) : ℝ) * a * g +
          25 * ((k - r : ℕ) : ℝ) * K * a ^ 2 +
          Λ * log (((k - r : ℕ) : ℝ) + 1)) ≤
      ((k : ℝ) + 2) ^ (C + Λ) *
        exp (-(k : ℝ) * a *
          (2 * S + (1 - τ) * g - τ * d - 3 * binEntropy τ) +
          a * ε + 25 * (k : ℝ) * K * a ^ 2) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hchoose : (0 : ℝ) < k.choose r := by
    exact_mod_cast Nat.choose_pos hrk
  have hlabel := mul_le_mul_of_nonpos_left hL (neg_nonpos.mpr ha)
  have hbad := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hr hd) ha
  have hgood := mul_le_mul_of_nonpos_right
    (show (1 - τ) * (k : ℝ) ≤ (k : ℝ) - r by nlinarith only [hr])
    (neg_nonpos.mpr (mul_nonneg ha hg))
  have hbinom := mul_le_mul_of_nonneg_left
    (log_choose_le_mul_binEntropy hτ hτhalf hr)
    (show 0 ≤ 3 * a by positivity)
  have hquad := mul_le_mul_of_nonneg_right
    (show (k : ℝ) - r ≤ k by linarith only [hr0])
    (show 0 ≤ 25 * K * a ^ 2 by positivity)
  have hlog := mul_le_mul_of_nonneg_left
    (log_le_log (by positivity : 0 < (((k - r : ℕ) : ℝ) + 1))
      (show (((k - r : ℕ) : ℝ) + 1) ≤ (k : ℝ) + 2 by
        rw [Nat.cast_sub hrk]
        linarith only [hr0])) hΛ
  have hexponent :
      log (k.choose r : ℝ) * a -
          a * (L - (r : ℝ) * d - 2 * log (k.choose r : ℝ)) +
          (-((k - r : ℕ) : ℝ) * a * g +
            25 * ((k - r : ℕ) : ℝ) * K * a ^ 2 +
            Λ * log (((k - r : ℕ) : ℝ) + 1)) ≤
        log ((k : ℝ) + 2) * Λ +
          (-(k : ℝ) * a *
            (2 * S + (1 - τ) * g - τ * d - 3 * binEntropy τ) +
            a * ε + 25 * (k : ℝ) * K * a ^ 2) := by
    rw [Nat.cast_sub hrk] at hlog ⊢
    nlinarith only [hlabel, hbad, hgood, hbinom, hquad, hlog]
  rw [rpow_def_of_pos hchoose, rpow_add (by positivity : 0 < (k : ℝ) + 2),
    rpow_def_of_pos (by positivity : 0 < (k : ℝ) + 2) Λ]
  simp only [mul_assoc, ← exp_add]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
    simpa only [sub_eq_add_neg, neg_mul, add_assoc, mul_assoc] using hexponent))
    (rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 2) C)

end Real
