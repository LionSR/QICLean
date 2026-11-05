/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InterleavedCountPolynomialBound

/-!
# Gap dependence of the interleaved output degree

The explicit degree produced by the variable-count polynomial estimate is
bounded by a tenth power of the physical logarithmic scale divided by the
square of the capped gap. These are scalar estimates for the same output
construction, supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817.
They do not assert a running time or a bound for the polynomial coefficient.
-/

namespace Real

/-- The exact natural degree chosen by the complete variable-count output
bound, supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. -/
noncomputable def interleavedOutputPolynomialDegree (g u K KD : ℝ) : ℕ :=
  let p := Nat.ceil (2 * KD)
  let p0 := Nat.ceil (K * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u))
  10 * (24 * p + 21) * p0 + 60 * p + 43

/-- The actual linear-logarithmic count coefficient has one explicit
seventh-power majorant. The gap is capped by one, as in the physical
interleaved construction supporting ALVV, lines 1797–1805. -/
theorem interleaved_count_coefficient_le (A U g : ℝ)
    (hA : 0 ≤ A) (hU : 1 ≤ U) (hg : 0 < g) (hg1 : g ≤ 1) :
    A * ((U + 17) ^ 7 / g + (U + 17) ^ 4 / sqrt g) ≤
      (A * (18 ^ 7 + 18 ^ 4)) * U ^ 7 / g := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hU17 : U + 17 ≤ 18 * U := by linarith only [hU]
  have hpow : U ^ 4 ≤ U ^ 7 := by gcongr; norm_num
  have hsqrt : g ≤ sqrt g := by
    apply (le_sqrt (by positivity) (by positivity)).mpr
    nlinarith only [hg, hg1]
  calc
    _ ≤ A * ((18 * U) ^ 7 / g + (18 * U) ^ 4 / g) := by gcongr
    _ ≤ A * ((18 * U) ^ 7 / g + 18 ^ 4 * U ^ 7 / g) := by
      rw [mul_pow (18 : ℝ) U 4]
      gcongr
    _ = _ := by rw [mul_pow]; ring

/-- An explicit bound for the degree chosen by the complete interleaved
output estimate. The count coefficient and reference profile are retained;
no fixed-count replacement is used. Supporting ALVV, arXiv:1602.08828v2,
lines 1797–1817, within the calibrated construction. -/
theorem interleaved_output_polynomial_degree_le
    (U u g K KD CK : ℝ)
    (hU : 1 ≤ U) (hu : 0 ≤ u) (huU : u ≤ U)
    (hg : 0 < g) (hg1 : g ≤ 1) (hK : 0 ≤ K) (hKD : 0 ≤ KD) (hCK : 0 ≤ CK)
    (hcount : KD ≤ CK * U ^ 7 / g) :
    let p := Nat.ceil (2 * KD)
    let p0 := Nat.ceil (K * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u))
    ((10 * (24 * p + 21) * p0 + 60 * p + 43 : ℕ) : ℝ) ≤
      (10 * (24 * (2 * CK + 1) + 21) * (6 * K + 1) +
        60 * (2 * CK + 1) + 43) * U ^ 10 / g ^ 2 := by
  intro p p0
  rw [mul_div_assoc] at hcount
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hrpow : (1 / g) ^ (1 / 4 : ℝ) ≤ 1 / g :=
    rpow_le_self_of_one_le hgInv (by norm_num)
  have hU3 : U ≤ U ^ 3 := by
    calc
      U = U ^ 1 := (pow_one _).symm
      _ ≤ _ := by gcongr; norm_num
  have hscale7 : 1 ≤ U ^ 7 / g :=
    (le_div_iff₀ hg).mpr (by simpa using hg1.trans (one_le_pow₀ hU))
  have hscale3 : 1 ≤ U ^ 3 / g :=
    (le_div_iff₀ hg).mpr (by simpa using hg1.trans (one_le_pow₀ hU))
  have hp : (p : ℝ) ≤ (2 * CK + 1) * (U ^ 7 / g) := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * KD)).le
    change (p : ℝ) ≤ 2 * KD + 1 at hceil
    nlinarith only [hceil, hcount, hscale7]
  have hraw : K * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u) ≤
      6 * K * (U ^ 3 / g) := by
    calc
      _ ≤ K * (U ^ 3 / g + 5 * (1 / g) * U ^ 3) := by
        gcongr
        exact huU.trans hU3
      _ = _ := by ring
  have hp0 : (p0 : ℝ) ≤ (6 * K + 1) * (U ^ 3 / g) := by
    have hceil := (Nat.ceil_lt_add_one
      (by positivity : 0 ≤ K * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u))).le
    change (p0 : ℝ) ≤ K * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u) + 1 at hceil
    nlinarith only [hceil, hraw, hscale3]
  have hprod : (U ^ 7 / g) * (U ^ 3 / g) = U ^ 10 / g ^ 2 := by ring
  have htail : U ^ 7 / g ≤ U ^ 10 / g ^ 2 := by
    rw [← hprod]
    exact le_mul_of_one_le_right (by positivity) hscale3
  have hone : 1 ≤ U ^ 10 / g ^ 2 := by
    rw [← hprod]
    exact one_le_mul_of_one_le_of_one_le hscale7 hscale3
  have hpTail : (p : ℝ) ≤ (2 * CK + 1) * (U ^ 10 / g ^ 2) :=
    hp.trans (mul_le_mul_of_nonneg_left htail (by positivity))
  have hfortyThree : 43 ≤ 43 * (U ^ 10 / g ^ 2) := by linarith only [hone]
  have hfirst : 24 * (p : ℝ) + 21 ≤ (24 * (2 * CK + 1) + 21) * (U ^ 7 / g) := by
    nlinarith only [hp, hscale7]
  push_cast
  calc
    _ ≤ 10 * ((24 * (2 * CK + 1) + 21) * (U ^ 7 / g)) *
        ((6 * K + 1) * (U ^ 3 / g)) +
        60 * ((2 * CK + 1) * (U ^ 10 / g ^ 2)) + 43 * (U ^ 10 / g ^ 2) := by
      gcongr
    _ = _ := by rw [← hprod]; ring

end Real
