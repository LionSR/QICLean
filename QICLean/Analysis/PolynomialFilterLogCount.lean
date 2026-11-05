/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PolynomialFilterCeil
import Mathlib.Tactic.NormNum

/-!
# Logarithms of the actual polynomial-filter counts

The base estimate and count calculation are adapted from
`TNLean/MPS/AreaLaw/PolynomialFilterParameters.lean` at commit
`ce9cbdeb7ac5212dcaa3344b7401ce2ca207adcc`. The base estimate keeps
its statement and proof, with a public mathematical name. The count
calculation is separated from the later absorption and suppression
argument, and reuses the existing ceiling bounds.

These scalar estimates support ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041, and Proposition `prop:albootstrap-ld`,
lines 1107–1128. No physical Hamiltonian or suppression bound is assumed.
-/

namespace Real

/-- The logarithm of the actual count base is linear in the logarithmic
scale. Scalar auxiliary for ALVV, t:ais, lines 1010--1024. -/
theorem log_polynomial_filter_base_le (A d g u e : ℝ) (hA : 1 ≤ A)
    (hd : 2 ≤ d) (hg : 0 < g) (hg1 : g ≤ 1)
    (hu : u = 1 + log d + log (1 / g))
    (he : 1 ≤ e) (heup : e ≤ (A + 1) * u ^ 2 / g) :
    log (d * e ^ 2) ≤ (6 + 2 * log (A + 1)) * u := by
  have hd0 : 0 < d := by linarith
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hld : 0 ≤ log d := log_nonneg (by linarith)
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := by linarith
  have he0 : 0 < e := by linarith
  have hAp : 0 < A + 1 := by linarith
  have hla : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hle : log e ≤ log (A + 1) + 2 * log u + log (1 / g) := by
    calc
      log e ≤ log ((A + 1) * u ^ 2 / g) := log_le_log he0 heup
      _ = log (A + 1) + 2 * log u + log (1 / g) := by
        rw [log_div (mul_ne_zero hAp.ne' (pow_ne_zero 2 hu0.ne')) hg.ne',
          log_mul hAp.ne' (pow_ne_zero 2 hu0.ne'), log_pow,
          one_div, log_inv]
        ring
  have hlu : log u ≤ u := log_le_self hu0.le
  have hldg : log d + 2 * log (1 / g) ≤ 2 * u := by rw [hu]; linarith
  have hlaMul : log (A + 1) ≤ log (A + 1) * u := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hla
  calc
    log (d * e ^ 2) = log d + 2 * log e := by
      rw [log_mul hd0.ne' (pow_ne_zero 2 he0.ne'), log_pow]
      norm_num
    _ ≤ log d + 2 * (log (A + 1) + 2 * log u + log (1 / g)) := by
      linarith only [hle]
    _ ≤ 2 * log (A + 1) + 6 * u := by
      linarith only [hlu, hldg]
    _ ≤ (6 + 2 * log (A + 1)) * u := by
      nlinarith only [hlaMul]

/-- The actual natural count has a positive value and explicit logarithmic
bounds for every admissible ceiling constant. The sharper linear-in-degree
bound is retained for the count-suppression argument. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem polynomial_filter_count_bounds (A : ℝ) (d : ℕ) (g : ℝ)
    (hA : 1 ≤ A) (hd : 2 ≤ d) (hg : 0 < g) (hg1 : g ≤ 1) :
    let u : ℝ := 1 + log (d : ℝ) + log (1 / g)
    let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
    let D : ℕ := (d * ell ^ 2) ^ (22 * ell)
    let cA : ℝ := 6 + 2 * log (A + 1)
    A * u ^ 2 / g ≤ (ell : ℝ) ∧
      (ell : ℝ) ≤ (A + 1) * u ^ 2 / g ∧ A ≤ (ell : ℝ) ∧
      0 < (D : ℝ) ∧ log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u ∧
      log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 := by
  intro u ell D cA
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : 0 < (d : ℝ) := by linarith
  have hld : 0 ≤ log (d : ℝ) := log_nonneg (by linarith)
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu1 : 1 ≤ u := by dsimp only [u]; linarith
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨hellLower, hellUpper, hellA⟩ :=
    ceil_quadratic_scale_bounds A u g hA hu1 hg hg1
  have hell1 : 1 ≤ (ell : ℝ) := hA.trans hellA
  have hcA0 : 0 ≤ cA := by
    dsimp only [cA]
    have := log_nonneg (show 1 ≤ A + 1 by linarith)
    linarith
  have hbase : log ((d : ℝ) * (ell : ℝ) ^ 2) ≤ cA * u :=
    log_polynomial_filter_base_le A d g u ell hA hdR hg hg1 rfl hell1 hellUpper
  have hDcast : (D : ℝ) = ((d : ℝ) * (ell : ℝ) ^ 2) ^ (22 * ell) := by
    simp only [D, Nat.cast_pow, Nat.cast_mul]
  have hDpos : 0 < (D : ℝ) := by rw [hDcast]; positivity
  have hlogD : log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u := by
    rw [hDcast, log_pow]
    have hmul := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 22 * (ell : ℝ) by positivity)
    push_cast
    nlinarith only [hmul]
  refine ⟨hellLower, hellUpper, hellA, hDpos, hlogD, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hellUpper
    (show 0 ≤ 22 * cA * u by positivity)
  calc
    log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u := hlogD
    _ ≤ 22 * ((A + 1) * u ^ 2 / g) * cA * u := by nlinarith only [hmul]
    _ = 22 * (A + 1) * cA / g * u ^ 3 := by ring

end Real
