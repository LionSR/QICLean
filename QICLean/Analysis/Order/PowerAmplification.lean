/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Scalar power amplification and weighted AM-GM bounds

This file collects elementary real-order lemmas used to amplify multiplicative
four-term coherence inequalities into sharp fourth-root bounds and to convert
coherence bounds into the linear Bell-overlap cap `(1 + √2) / 4`.

## Main results

* `Real.le_of_pow_le_const_mul_pow`: if `0 ≤ x`, `0 ≤ y`, and `x ^ t ≤ C * y ^ t`
  for all `t ≥ 1`, then `x ≤ y`.
* `Real.pow_four_le_of_rescaled_four_term_bound`: from `k ≤ √(p₀₀ p₁₁)` and the
  rescaled tensor-power four-term inequality
  `k ^ t ≤ λ √(p₀₀^t p₀₁^t) + λ⁻¹ √(p₁₀^t p₁₁^t) + 2 √(p₀₁^t p₁₀^t)`
  for all `t ≥ 1` and `λ > 0`, deduce `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁`, including all
  zero-population edge cases.
* `Real.le_half_sqrt_sum_mul_sum_of_pow_four_le`: `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁` implies
  `k ≤ (1 / 2) √((p₀₀ + p₁₁) (p₀₁ + p₁₀))`.
* `Real.two_mul_sqrt_mul_le_weighted_sum`: weighted AM-GM
  `2 √(s r) ≤ (√2 - 1) s + (√2 + 1) r` for `s, r ≥ 0`.
* `Real.half_add_sqrt_mul_le_bell_cap`:
  `(1 / 2) (s + √(s r)) ≤ ((1 + √2) / 4) (s + r)` for `s, r ≥ 0`.
-/

namespace Real

private theorem sqrt_pow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (t : ℕ) :
    Real.sqrt (x ^ t) = Real.sqrt x ^ t := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]

/-- **Elementary power amplification.** If `0 ≤ x`, `0 ≤ y`, and there is a constant `C`
such that `x ^ t ≤ C * y ^ t` for every `t ≥ 1`, then `x ≤ y`. -/
theorem le_of_pow_le_const_mul_pow {x y C : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ t : ℕ, 1 ≤ t → x ^ t ≤ C * y ^ t) : x ≤ y := by
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hy with rfl | hypos
  · have h1 := h 1 le_rfl
    simp only [pow_one, mul_zero] at h1
    linarith
  · have hr : 1 < x / y := (one_lt_div hypos).mpr hlt
    set δ : ℝ := x / y - 1
    have hδ : 0 < δ := sub_pos.mpr hr
    obtain ⟨n, hn⟩ := exists_nat_gt (max C 0 / δ)
    let t : ℕ := n + 1
    have ht1 : 1 ≤ t := Nat.succ_le_succ (Nat.zero_le n)
    have hpow : (x / y) ^ t ≤ C := by
      rw [div_pow, div_le_iff₀ (pow_pos hypos t)]
      exact h t ht1
    have hbern : 1 + (t : ℝ) * δ ≤ (x / y) ^ t := by
      have h1 : 1 + δ = x / y := by simp [δ]
      rw [← h1]
      exact one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) t
    have hgt : max C 0 < (t : ℝ) * δ := by
      have hn' : max C 0 / δ < (t : ℝ) := lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
      exact (div_lt_iff₀ hδ).mp hn'
    have hC : C ≤ max C 0 := le_max_left C 0
    linarith

/-- **Rescaling + power amplification for the four-term coherence inequality.**
Given nonnegative reals `k, p₀₀, p₀₁, p₁₀, p₁₁` satisfying the direct diagonal bound
`k ≤ √(p₀₀ p₁₁)` and the rescaled `t`-th power four-term inequality for all `t ≥ 1`
and `λ > 0`, we have `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁`. All zero-population cases are
handled explicitly without division by zero. -/
theorem pow_four_le_of_rescaled_four_term_bound
    {k p00 p01 p10 p11 : ℝ}
    (hk : 0 ≤ k) (hp00 : 0 ≤ p00) (hp01 : 0 ≤ p01) (hp10 : 0 ≤ p10) (hp11 : 0 ≤ p11)
    (hdiag : k ≤ Real.sqrt (p00 * p11))
    (hfour : ∀ (t : ℕ), 1 ≤ t → ∀ (lam : ℝ), 0 < lam →
      k ^ t ≤ lam * Real.sqrt (p00 ^ t * p01 ^ t) +
        lam⁻¹ * Real.sqrt (p10 ^ t * p11 ^ t) +
        2 * Real.sqrt (p01 ^ t * p10 ^ t)) :
    k ^ 4 ≤ p00 * p01 * p10 * p11 := by
  -- Zero-population cases: any vanishing population forces `k = 0`.
  rcases eq_or_lt_of_le hp00 with rfl | hp00_pos
  · have hk0 : k = 0 := le_antisymm (by simpa using hdiag) hk
    simp [hk0]
  rcases eq_or_lt_of_le hp11 with rfl | hp11_pos
  · have hk0 : k = 0 := le_antisymm (by simpa using hdiag) hk
    simp [hk0]
  rcases eq_or_lt_of_le hp01 with rfl | hp01_pos
  · have hk0 : k ≤ 0 := by
      by_contra hkpos
      push Not at hkpos
      set b : ℝ := Real.sqrt (p10 * p11)
      have hb : 0 ≤ b := Real.sqrt_nonneg _
      set lam : ℝ := (2 * b + 1) / k
      have hlam : 0 < lam := div_pos (by linarith) hkpos
      have h1 := hfour 1 le_rfl lam hlam
      simp only [pow_one, mul_zero, zero_mul, Real.sqrt_zero, zero_add, add_zero] at h1
      have hle : lam⁻¹ * b < k := by
        rw [inv_mul_eq_div, div_lt_iff₀ hlam]
        have hmul : k * lam = 2 * b + 1 := mul_div_cancel₀ (2 * b + 1) (ne_of_gt hkpos)
        linarith
      linarith
    have hk_eq : k = 0 := le_antisymm hk0 hk
    simp [hk_eq]
  rcases eq_or_lt_of_le hp10 with rfl | hp10_pos
  · have hk0 : k ≤ 0 := by
      by_contra hkpos
      push Not at hkpos
      set a : ℝ := Real.sqrt (p00 * p01)
      have ha : 0 ≤ a := Real.sqrt_nonneg _
      set lam : ℝ := k / (2 * a + 1)
      have hlam : 0 < lam := div_pos hkpos (by linarith)
      have h1 := hfour 1 le_rfl lam hlam
      simp only [pow_one, mul_zero, zero_mul, Real.sqrt_zero, add_zero] at h1
      have hle : lam * a < k := by
        rw [show lam * a = k * (a / (2 * a + 1)) by simp [lam]; ring]
        have hfrac : a / (2 * a + 1) < 1 := by
          rw [div_lt_one (by linarith)]
          linarith
        nlinarith
      linarith
    have hk_eq : k = 0 := le_antisymm hk0 hk
    simp [hk_eq]
  -- Strictly positive case: all four populations are positive.
  set a : ℝ := Real.sqrt (p00 * p01)
  set b : ℝ := Real.sqrt (p10 * p11)
  set g : ℝ := Real.sqrt (a * b)
  set h : ℝ := Real.sqrt (p01 * p10)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (mul_pos hp00_pos hp01_pos)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (mul_pos hp10_pos hp11_pos)
  have hg_pos : 0 < g := Real.sqrt_pos.mpr (mul_pos ha_pos hb_pos)
  have hh_pos : 0 < h := Real.sqrt_pos.mpr (mul_pos hp01_pos hp10_pos)
  have hg2 : g ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha_pos.le hb_pos.le)
  have hg4 : g ^ 4 = p00 * p01 * p10 * p11 := by
    have hpow4 : g ^ 4 = (g ^ 2) ^ 2 := by ring
    rw [hpow4, hg2, mul_pow, Real.sq_sqrt (mul_nonneg hp00 hp01),
      Real.sq_sqrt (mul_nonneg hp10 hp11)]
    ring
  have hkg : k ≤ g := by
    by_cases hhg : h ≤ g
    · refine le_of_pow_le_const_mul_pow hk hg_pos.le (C := 4) fun t ht => ?_
      set r : ℝ := Real.sqrt (b / a)
      have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos hb_pos ha_pos)
      have hlam_pos : 0 < r ^ t := pow_pos hr_pos t
      have hstep := hfour t ht (r ^ t) hlam_pos
      have hp00_01 : Real.sqrt (p00 ^ t * p01 ^ t) = a ^ t := by
        rw [← mul_pow, sqrt_pow_of_nonneg (mul_nonneg hp00 hp01)]
      have hp10_11 : Real.sqrt (p10 ^ t * p11 ^ t) = b ^ t := by
        rw [← mul_pow, sqrt_pow_of_nonneg (mul_nonneg hp10 hp11)]
      have hp01_10 : Real.sqrt (p01 ^ t * p10 ^ t) = h ^ t := by
        rw [← mul_pow, sqrt_pow_of_nonneg (mul_nonneg hp01 hp10)]
      have hra : r * a = g := by
        have h1 : (r * a) ^ 2 = g ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (div_nonneg hb_pos.le ha_pos.le), hg2]
          field_simp [ne_of_gt ha_pos]
        nlinarith [mul_pos hr_pos ha_pos, hg_pos]
      have hrb : r⁻¹ * b = g := by
        have h1 : (r⁻¹ * b) ^ 2 = g ^ 2 := by
          rw [mul_pow, inv_pow, Real.sq_sqrt (div_nonneg hb_pos.le ha_pos.le), hg2]
          field_simp [ne_of_gt ha_pos, ne_of_gt hb_pos]
        nlinarith [mul_pos (inv_pos.mpr hr_pos) hb_pos, hg_pos]
      rw [hp00_01, hp10_11, hp01_10, ← mul_pow, hra, ← inv_pow, ← mul_pow, hrb] at hstep
      have hht : h ^ t ≤ g ^ t := pow_le_pow_left₀ hh_pos.le hhg t
      linarith
    · push Not at hhg
      have hgh : g ^ 2 = Real.sqrt (p00 * p11) * h := by
        rw [hg2, ← Real.sqrt_mul (mul_nonneg hp00 hp01), ← Real.sqrt_mul (mul_nonneg hp00 hp11)]
        congr 1
        ring
      have hkh : k * h ≤ g ^ 2 := by
        rw [hgh]
        exact mul_le_mul_of_nonneg_right hdiag hh_pos.le
      nlinarith
  calc
    k ^ 4 ≤ g ^ 4 := pow_le_pow_left₀ hk hkg 4
    _ = p00 * p01 * p10 * p11 := hg4

/-- From `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁` with nonnegative variables, AM-GM on the two
diagonal pairs yields `k ≤ (1 / 2) √((p₀₀ + p₁₁) (p₀₁ + p₁₀))`. -/
theorem le_half_sqrt_sum_mul_sum_of_pow_four_le
    {k p00 p01 p10 p11 : ℝ}
    (hk : 0 ≤ k) (hp00 : 0 ≤ p00) (hp01 : 0 ≤ p01) (hp10 : 0 ≤ p10) (hp11 : 0 ≤ p11)
    (h4 : k ^ 4 ≤ p00 * p01 * p10 * p11) :
    k ≤ (1 / 2 : ℝ) * Real.sqrt ((p00 + p11) * (p01 + p10)) := by
  have hs : 4 * (p00 * p11) ≤ (p00 + p11) ^ 2 := by nlinarith [sq_nonneg (p00 - p11)]
  have hr : 4 * (p01 * p10) ≤ (p01 + p10) ^ 2 := by nlinarith [sq_nonneg (p01 - p10)]
  have hprod : 16 * (p00 * p01 * p10 * p11) ≤ ((p00 + p11) * (p01 + p10)) ^ 2 := by
    have hmul := mul_le_mul hs hr (by positivity) (sq_nonneg _)
    nlinarith
  have h16 : (2 * k) ^ 4 ≤ ((p00 + p11) * (p01 + p10)) ^ 2 := by
    calc
      (2 * k) ^ 4 = 16 * k ^ 4 := by ring
      _ ≤ 16 * (p00 * p01 * p10 * p11) := by linarith
      _ ≤ ((p00 + p11) * (p01 + p10)) ^ 2 := hprod
  have hsq : (2 * k) ^ 2 ≤ (p00 + p11) * (p01 + p10) := by
    have hnonneg : 0 ≤ (p00 + p11) * (p01 + p10) := by positivity
    nlinarith [sq_nonneg ((2 * k) ^ 2 - (p00 + p11) * (p01 + p10)),
      show ((2 * k) ^ 2) ^ 2 = (2 * k) ^ 4 by ring]
  have h2k : 2 * k ≤ Real.sqrt ((p00 + p11) * (p01 + p10)) := by
    rw [Real.le_sqrt (by linarith) (by positivity)]
    exact hsq
  linarith

/-- **Weighted AM-GM for the Bell-overlap cap:**
`2 √(s r) ≤ (√2 - 1) s + (√2 + 1) r` for all `s, r ≥ 0`. -/
theorem two_mul_sqrt_mul_le_weighted_sum {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    2 * Real.sqrt (s * r) ≤ (Real.sqrt 2 - 1) * s + (Real.sqrt 2 + 1) * r := by
  have h2gt1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hα : 0 ≤ Real.sqrt 2 - 1 := by linarith
  have hβ : 0 ≤ Real.sqrt 2 + 1 := by linarith
  have hαβ : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hsq := sq_nonneg (Real.sqrt (Real.sqrt 2 - 1) * Real.sqrt s -
    Real.sqrt (Real.sqrt 2 + 1) * Real.sqrt r)
  have hexp :
      (Real.sqrt (Real.sqrt 2 - 1) * Real.sqrt s -
        Real.sqrt (Real.sqrt 2 + 1) * Real.sqrt r) ^ 2 =
      (Real.sqrt 2 - 1) * s + (Real.sqrt 2 + 1) * r - 2 * Real.sqrt (s * r) := by
    have hcross :
        Real.sqrt (Real.sqrt 2 - 1) * Real.sqrt s *
          (Real.sqrt (Real.sqrt 2 + 1) * Real.sqrt r) = Real.sqrt (s * r) := by
      calc
        Real.sqrt (Real.sqrt 2 - 1) * Real.sqrt s *
            (Real.sqrt (Real.sqrt 2 + 1) * Real.sqrt r)
          = (Real.sqrt (Real.sqrt 2 - 1) * Real.sqrt (Real.sqrt 2 + 1)) *
              (Real.sqrt s * Real.sqrt r) := by ring
        _ = Real.sqrt ((Real.sqrt 2 - 1) * (Real.sqrt 2 + 1)) * Real.sqrt (s * r) := by
            rw [← Real.sqrt_mul hα, ← Real.sqrt_mul hs]
        _ = Real.sqrt (s * r) := by rw [hαβ, Real.sqrt_one, one_mul]
    have h1 : (Real.sqrt (Real.sqrt 2 - 1) * Real.sqrt s) ^ 2 = (Real.sqrt 2 - 1) * s := by
      rw [mul_pow, Real.sq_sqrt hα, Real.sq_sqrt hs]
    have h2 : (Real.sqrt (Real.sqrt 2 + 1) * Real.sqrt r) ^ 2 = (Real.sqrt 2 + 1) * r := by
      rw [mul_pow, Real.sq_sqrt hβ, Real.sq_sqrt hr]
    nlinarith
  linarith

/-- **Linear Bell-overlap cap from weighted AM-GM:**
`(1 / 2) (s + √(s r)) ≤ ((1 + √2) / 4) (s + r)` for all `s, r ≥ 0`. -/
theorem half_add_sqrt_mul_le_bell_cap {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    (1 / 2 : ℝ) * (s + Real.sqrt (s * r)) ≤ ((1 + Real.sqrt 2) / 4) * (s + r) := by
  have h := two_mul_sqrt_mul_le_weighted_sum hs hr
  linarith

end Real
