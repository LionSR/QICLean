/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InterleavedCountPolynomialBound

/-!
# Polynomial costs for the variable interleaved count

The independent truncation calibration gives a count depending on length and
ground multiplicity. A linear logarithmic bound controls this actual count,
the nominal sampling size and their subsequent scalar costs. These are
numerical auxiliaries to ALVV, arXiv:1602.08828v2, lines 1797–1817; no
printed sharp count profile, physical construction or running time is asserted.
-/

namespace Real

/-- The actual independent-scale logarithmic estimate is linear in the
chain-size logarithm, at fixed physical parameters. Supporting ALVV,
arXiv:1602.08828v2, lines 1797–1805, for the corrected interleaved scales. -/
theorem interleaved_log_bound_le_linear (A g U w x : ℝ)
    (hA : 0 ≤ A) (hg : 0 < g) (hU : 1 ≤ U) (hw : 1 ≤ w)
    (hx : x ≤ A * ((U + log (1 + w)) ^ 7 / g +
      sqrt w * (U + log (1 + w)) ^ 4 / sqrt g)) :
    x ≤ A * ((U + 17) ^ 7 / g + (U + 17) ^ 4 / sqrt g) * w := by
  obtain ⟨hfirst, hsecond⟩ := interleaved_log_powers_le_linear hU hw
  calc
    _ ≤ A * ((U + log (1 + w)) ^ 7 / g +
        sqrt w * (U + log (1 + w)) ^ 4 / sqrt g) := hx
    _ ≤ A * (((U + 17) ^ 7 * w) / g + ((U + 17) ^ 4 * w) / sqrt g) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_right hfirst hg.le)
        (div_le_div_of_nonneg_right hsecond (sqrt_nonneg _))) hA
    _ = _ := by ring

/-- The logarithmic length and multiplicity scale is bounded by the
logarithm of any common size majorant. Supporting ALVV,
arXiv:1602.08828v2, lines 1797–1805. -/
theorem interleaved_size_log_bounds {r l Z : ℝ}
    (hr : 1 ≤ r) (hl : 1 ≤ l) (hrl : r * l ≤ Z) :
    1 ≤ Z ∧ r ≤ Z ∧ l ≤ Z ∧
      1 ≤ 1 + log r + 2 * log l ∧
      1 + log r + 2 * log l ≤ 1 + 2 * log Z ∧
      1 + log r + 2 * log l ≤ 2 * Z := by
  have hr0 : 0 < r := by linarith only [hr]
  have hl0 : 0 < l := by linarith only [hl]
  have hrl1 : 1 ≤ r * l := one_le_mul_of_one_le_of_one_le hr hl
  have hZ : 1 ≤ Z := hrl1.trans hrl
  have hrZ : r ≤ Z := (le_mul_of_one_le_right hr0.le hl).trans hrl
  have hlZ : l ≤ Z := (le_mul_of_one_le_left hl0.le hr).trans hrl
  have hlogr : 0 ≤ log r := log_nonneg hr
  have hlogl : 0 ≤ log l := log_nonneg hl
  have hlogs := log_le_log (mul_pos hr0 hl0) hrl
  rw [log_mul hr0.ne' hl0.ne'] at hlogs
  refine ⟨hZ, hrZ, hlZ, by linarith only [hlogr, hlogl], ?_, ?_⟩
  · linarith only [hlogs, hlogr]
  · have hlogZ := log_le_sub_one_of_pos (by linarith only [hZ] : 0 < Z)
    linarith only [hlogs, hlogr, hlogZ]

/-- A linear logarithmic bound on the SAME count and its actual sampling
ceiling gives uniform polynomial bounds with explicit constants. The
coefficient and exponent depend only on `K`, not on length or multiplicity.
Supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. -/
theorem interleaved_count_sample_polynomial_bounds (K : ℝ) (hK : 0 ≤ K)
    (D s : ℕ) (hD : 1 ≤ D) (r l Z : ℝ)
    (hr : 1 ≤ r) (hl : 1 ≤ l) (hrl : r * l ≤ Z)
    (hlogD : log (D : ℝ) ≤ K * (1 + log r + 2 * log l))
    (hs : (s : ℝ) ≤ 4097 * r * (log (D : ℝ) + (1 + log r + 2 * log l))) :
    (D : ℝ) ≤ exp K * Z ^ Nat.ceil (2 * K) ∧
      (s : ℝ) ≤ (8194 * (K + 1)) * Z ^ 2 := by
  obtain ⟨hZ, hrZ, _hlZ, hw, hwLog, hwZ⟩ := interleaved_size_log_bounds hr hl hrl
  have hZ0 : 0 < Z := by linarith only [hZ]
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlog : log (D : ℝ) ≤ K + (2 * K) * log Z := by
    have hb := mul_le_mul_of_nonneg_left hwLog hK
    nlinarith only [hlogD, hb]
  constructor
  · calc
      (D : ℝ) = exp (log (D : ℝ)) := (exp_log hD0).symm
      _ ≤ exp (K + (2 * K) * log Z) := exp_le_exp.mpr hlog
      _ = exp K * Z ^ (2 * K) := by
        rw [exp_add, rpow_def_of_pos hZ0, mul_comm (log Z) (2 * K)]
      _ ≤ exp K * Z ^ Nat.ceil (2 * K) := by
        simpa only [rpow_natCast] using mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_exponent_le hZ (Nat.le_ceil (2 * K))) (exp_pos K).le
  · have hinner : log (D : ℝ) + (1 + log r + 2 * log l) ≤
        (K + 1) * (2 * Z) := by
      have hb := mul_le_mul_of_nonneg_left hwZ (by linarith only [hK] : 0 ≤ K + 1)
      nlinarith only [hlogD, hb]
    calc
      (s : ℝ) ≤ 4097 * r * (log (D : ℝ) + (1 + log r + 2 * log l)) := hs
      _ ≤ 4097 * Z * ((K + 1) * (2 * Z)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hrZ (by norm_num)) hinner
        · have hlogD0 : 0 ≤ log (D : ℝ) := log_nonneg (by exact_mod_cast hD)
          linarith only [hlogD0, hw]
        · positivity
      _ = _ := by ring

/-- The actual overlap and clipping accuracies have explicit reciprocal
monomials. Supporting the calibrated ALVV interleaved construction,
arXiv:1602.08828v2, lines 1797–1805. -/
theorem interleaved_inverse_accuracy_identities (D s : ℝ) (hD : 0 < D) (hs : 0 < s) :
    let a := 3 / (32 * D ^ 12 * s ^ 5)
    let tau := a ^ 2 / 1048576
    1 / a = (32 / 3 : ℝ) * D ^ 12 * s ^ 5 ∧
      1 / tau = (1073741824 / 9 : ℝ) * D ^ 24 * s ^ 10 := by
  intro a tau
  constructor <;> dsimp only [a, tau] <;> field_simp
  all_goals ring

/-- Polynomial count and sample bounds control the actual clipping accuracy
and the ceiling used to select one common refinement radius. The exponents
retain the count's variable polynomial degree. Supporting ALVV,
arXiv:1602.08828v2, lines 1797–1817, for the calibrated interleaved scales. -/
theorem interleaved_inverse_cost_polynomial_bounds
    (D s p : ℕ) (hD : 1 ≤ D) (hs : 1 ≤ s) (Z CD Cs : ℝ)
    (hZ : 1 ≤ Z) (hCD : 1 ≤ CD) (hCs : 1 ≤ Cs)
    (hDpoly : (D : ℝ) ≤ CD * Z ^ p) (hSpoly : (s : ℝ) ≤ Cs * Z ^ 2) :
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    0 < a ∧ a ≤ 1 ∧ 0 < tau ∧ tau ≤ 1 ∧
      1 / tau ≤ (1 + 1073741824 * CD ^ 24 * Cs ^ 10) * Z ^ (24 * p + 20) ∧
      (Nat.ceil (1 / a) : ℝ) ≤ (1 + 32 * CD ^ 12 * Cs ^ 5) * Z ^ (12 * p + 10) := by
  intro a tau
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hD0 : (0 : ℝ) < D := by linarith only [hDR]
  have hs0 : (0 : ℝ) < s := by linarith only [hsR]
  have hCD0 : 0 ≤ CD := by linarith only [hCD]
  have hCs0 : 0 ≤ Cs := by linarith only [hCs]
  have hZ0 : 0 ≤ Z := by linarith only [hZ]
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a ≤ 1 := by
    have hprod : 1 ≤ (D : ℝ) ^ 12 * (s : ℝ) ^ 5 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hDR) (one_le_pow₀ hsR)
    dsimp only [a]
    apply (div_le_one (by positivity)).mpr
    nlinarith only [hprod]
  have htau : 0 < tau := by dsimp only [tau]; positivity
  have htau1 : tau ≤ 1 := by
    have hasq : a ^ 2 ≤ 1 := by nlinarith only [ha, ha1]
    dsimp only [tau]
    linarith only [hasq]
  obtain ⟨haInv, htauInv⟩ := interleaved_inverse_accuracy_identities (D : ℝ) s hD0 hs0
  change 1 / a = _ at haInv
  change 1 / tau = _ at htauInv
  have haBound : 1 / a ≤ 32 * CD ^ 12 * Cs ^ 5 * Z ^ (12 * p + 10) := by
    calc
      _ = (32 / 3 : ℝ) * (D : ℝ) ^ 12 * (s : ℝ) ^ 5 := haInv
      _ ≤ 32 * (CD * Z ^ p) ^ 12 * (Cs * Z ^ 2) ^ 5 := by gcongr; norm_num
      _ = _ := by simp only [mul_pow, pow_add, pow_mul]; ring
  have htauBound : 1 / tau ≤ 1073741824 * CD ^ 24 * Cs ^ 10 * Z ^ (24 * p + 20) := by
    calc
      _ = (1073741824 / 9 : ℝ) * (D : ℝ) ^ 24 * (s : ℝ) ^ 10 := htauInv
      _ ≤ 1073741824 * (CD * Z ^ p) ^ 24 * (Cs * Z ^ 2) ^ 10 := by gcongr; norm_num
      _ = _ := by simp only [mul_pow, pow_add, pow_mul]; ring
  refine ⟨ha, ha1, htau, htau1, ?_, ?_⟩
  · exact htauBound.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)) (pow_nonneg hZ0 _))
  · have hceil := (Nat.ceil_lt_add_one (one_div_nonneg.mpr ha.le)).le
    have hpower : (1 : ℝ) ≤ Z ^ (12 * p + 10) := one_le_pow₀ hZ
    nlinarith only [hceil, haBound, hpower]

end Real
