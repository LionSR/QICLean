/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PolynomialFilterCeil

/-!
# Dyadic growth of polynomial-filter counts

The count is evaluated at the actual natural ceiling of the filter scale.
A fixed large count base absorbs the finite rounding terms in the dyadic
argument of ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. This is a scalar auxiliary; no physical rank or suppression
estimate is an assumption or conclusion.
-/

namespace Real

/-- Halving the width enlarges the logarithm of the actual natural count by
at most `13/6`. The count base is fixed before both widths. This finite-scale
auxiliary supports ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem log_polynomial_filter_count_half_step (A : ℝ) (m : ℕ) (g h : ℝ)
    (hA : 100 ≤ A) (hm : 100 ≤ log (m : ℝ))
    (hg : 0 < g) (hg1 : g ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhalf : g ≤ 2 * h) :
    let u := 1 + log (m : ℝ) + log (1 / g)
    let v := 1 + log (m : ℝ) + log (1 / h)
    let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
    let ell' : ℕ := ⌈A * v ^ 2 / h⌉₊
    let D := (m * ell ^ 2) ^ (22 * ell)
    let D' := (m * ell' ^ 2) ^ (22 * ell')
    100 ≤ log (D : ℝ) ∧ log (D' : ℝ) ≤ (13 / 6) * log (D : ℝ) := by
  intro u v ell ell' D D'
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogh : 0 ≤ log (1 / h) := log_nonneg ((one_le_div hh).mpr hh1)
  have hu : 100 ≤ u := by dsimp only [u]; linarith only [hm, hlogg]
  have hv : 1 ≤ v := by dsimp only [v]; linarith only [hm, hlogh]
  have hinv : 1 / h ≤ 2 / g :=
    (div_le_div_iff₀ hh hg).mpr (by simpa only [one_mul] using hhalf)
  have hlogratio : log (1 / h) ≤ log (1 / g) + 1 := by
    have hb := log_le_log (by positivity : 0 < 1 / h) hinv
    rw [show (2 : ℝ) / g = 2 * (1 / g) by ring,
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (1 / g) ≠ 0)] at hb
    have hlog2 : log (2 : ℝ) ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
        log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hb, hlog2]
  obtain ⟨hellA, hellA', hscale⟩ :=
    ceil_quadratic_scale_half_step A u v g h hA hu hv
      (by dsimp only [u, v]; linarith only [hlogratio]) hg hg1 hh hh1 hhalf
  have hell : 100 ≤ (ell : ℝ) := hA.trans hellA
  have hell' : 100 ≤ (ell' : ℝ) := hA.trans hellA'
  have hell0 : 0 < (ell : ℝ) := by linarith only [hell]
  have hell'0 : 0 < (ell' : ℝ) := by linarith only [hell']
  have hm_nat : m ≠ 0 := by rintro rfl; norm_num at hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm_nat
  let B := log (m : ℝ) + 2 * log (ell : ℝ)
  let B' := log (m : ℝ) + 2 * log (ell' : ℝ)
  have hB : 100 ≤ B := by
    have hb := log_nonneg (show 1 ≤ (ell : ℝ) by linarith only [hell])
    dsimp only [B]
    linarith only [hm, hb]
  have hlogscale : log (ell' : ℝ) ≤ log (ell : ℝ) + 11 / 10 := by
    have hb := log_le_log hell'0 hscale
    rw [log_mul (by norm_num : (21 / 10 : ℝ) ≠ 0) hell0.ne'] at hb
    have hlogratio' : log (21 / 10 : ℝ) ≤ 11 / 10 := by
      simpa only [show (21 / 10 : ℝ) - 1 = 11 / 10 by norm_num] using
        log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 10)
    linarith only [hb, hlogratio']
  have hBscale : B' ≤ (511 / 500) * B := by
    dsimp only [B, B'] at *
    linarith only [hB, hlogscale]
  have hcountLog (n : ℕ) (hn : 0 < (n : ℝ)) :
      log ((((m * n ^ 2) ^ (22 * n)) : ℕ) : ℝ) =
        22 * (n : ℝ) * (log (m : ℝ) + 2 * log (n : ℝ)) := by
    simp only [Nat.cast_pow, Nat.cast_mul, log_pow,
      log_mul hm0.ne' (pow_ne_zero 2 hn.ne')]
    push_cast
    ring
  have hlogD : log (D : ℝ) = 22 * (ell : ℝ) * B := hcountLog ell hell0
  have hlogD' : log (D' : ℝ) = 22 * (ell' : ℝ) * B' := hcountLog ell' hell'0
  rw [hlogD, hlogD']
  refine ⟨by nlinarith only [hB, hell], ?_⟩
  calc
    22 * (ell' : ℝ) * B' ≤ 22 * ((21 / 10) * (ell : ℝ)) * ((511 / 500) * B) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hscale (by norm_num)) hBscale
        (by dsimp only [B']; positivity) (by positivity)
    _ ≤ (13 / 6) * (22 * (ell : ℝ) * B) := by
      nlinarith only [mul_nonneg hell0.le (show 0 ≤ B by linarith only [hB])]

end Real
