/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.InterleavedPolynomialDegree
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Gap dependence of the interleaved output coefficient

The logarithm of the coefficient selected by the actual variable-count
construction has the same tenth-power logarithmic scale divided by the square
of the capped gap. These numerical estimates support ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1777–1817; no running time is asserted.
-/

namespace Real

private theorem log_one_add_mul_pow_mul_pow_le (a b c : ℝ) (n m : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    log (1 + a * b ^ n * c ^ m) ≤ 1 + log a + n * log b + m * log c := by
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := by linarith only [hb]
  have hc0 : 0 < c := by linarith only [hc]
  have hx : 1 ≤ a * b ^ n * c ^ m := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le ha (one_le_pow₀ hb)) (one_le_pow₀ hc)
  have hlog := log_one_add_le_posLog (x := a * b ^ n * c ^ m)
  rw [posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact hx),
    log_mul (by positivity) (by positivity), log_mul ha0.ne' (by positivity),
    log_pow, log_pow] at hlog
  have htwo := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith only [hlog, htwo]

/-- The coefficient selected by the complete variable-count interleaved
output estimate, supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. -/
noncomputable def interleavedOutputPolynomialCoefficient (gamma g u K KD : ℝ) : ℝ :=
  let CD := exp KD
  let Cs := 8194 * (KD + 1)
  let Ct := 1 + 1073741824 * CD ^ 24 * Cs ^ 10
  let CNtree := 1 + 32 * CD ^ 12 * Cs ^ 5
  let J := 1 + 1 / gamma
  let Kc := 6 * J ^ 2
  let Ke := 196608 * J ^ 3
  let Kcost := max Ct Ke
  let a0 := u ^ 3 / g
  let a1 := (1 / g) ^ (1 / 4 : ℝ) * u
  let b0 := 16 + log (1 / g) + log (32 * Kcost)
  let CB := exp (K * (a0 + 5 * a1) * b0)
  let Ccommon := CB * CNtree
  let CN := 1 + 100 * CD ^ 12 * Kc
  let CM := CD ^ 6 * Cs ^ 3
  let Cpoly := 1 + 1000000 * (Ccommon * CN) ^ 2 * CM ^ 2
  Cpoly

/-- A factored bound for the logarithm of the actual selected coefficient.
The length and ground multiplicity do not occur. Supporting the calibrated
interleaved construction for ALVV, arXiv:1602.08828v2, lines 1797–1817. -/
theorem log_interleavedOutputPolynomialCoefficient_le
    (gamma g u K KD : ℝ) (hgamma : 0 < gamma) (hg : 0 < g) (hg1 : g ≤ 1)
    (hu : 0 ≤ u) (hK : 0 ≤ K) (hKD : 0 ≤ KD) :
    log (max (interleavedOutputPolynomialCoefficient gamma g u K KD) 1) ≤
      10000000 * (K + 1) * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u + 1) *
        (1 + KD + log (1 / g) + log (1 + 1 / gamma)) := by
  let CD := exp KD
  let Cs := 8194 * (KD + 1)
  let Ct := 1 + 1073741824 * CD ^ 24 * Cs ^ 10
  let CNtree := 1 + 32 * CD ^ 12 * Cs ^ 5
  let J := 1 + 1 / gamma
  let Kc := 6 * J ^ 2
  let Ke := 196608 * J ^ 3
  let Kcost := max Ct Ke
  let a0 := u ^ 3 / g
  let a1 := (1 / g) ^ (1 / 4 : ℝ) * u
  let b0 := 16 + log (1 / g) + log (32 * Kcost)
  let CB := exp (K * (a0 + 5 * a1) * b0)
  let Ccommon := CB * CNtree
  let CN := 1 + 100 * CD ^ 12 * Kc
  let CM := CD ^ 6 * Cs ^ 3
  let Cpoly := 1 + 1000000 * (Ccommon * CN) ^ 2 * CM ^ 2
  have hCD : 1 ≤ CD := one_le_exp_iff.mpr hKD
  have hCs : 1 ≤ Cs := by dsimp only [Cs]; linarith only [hKD]
  have hCt : 1 ≤ Ct := by
    have hn : 0 ≤ 1073741824 * CD ^ 24 * Cs ^ 10 := by positivity
    dsimp only [Ct]
    linarith only [hn]
  have hCNtree : 1 ≤ CNtree := by
    have hn : 0 ≤ 32 * CD ^ 12 * Cs ^ 5 := by positivity
    dsimp only [CNtree]
    linarith only [hn]
  have hKcost : 1 ≤ Kcost := hCt.trans (le_max_left Ct Ke)
  let X := 1 + KD + log (1 / g) + log J
  let Y := a0 + 5 * a1
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hJ : 1 ≤ J := by dsimp only [J]; linarith [one_div_pos.mpr hgamma]
  have hlogg : 0 ≤ log (1 / g) := log_nonneg hgInv
  have hlogJ : 0 ≤ log J := log_nonneg hJ
  have hX : 1 ≤ X := by dsimp only [X]; linarith only [hKD, hlogg, hlogJ]
  have hY : 0 ≤ Y := by dsimp only [Y, a0, a1]; positivity
  have hCB : 1 ≤ CB := one_le_exp_iff.mpr (by
    have hb0 : 0 ≤ b0 := by
      dsimp only [b0]
      have hcost : 0 ≤ log (32 * Kcost) := log_nonneg (by linarith only [hKcost])
      linarith only [hlogg, hcost]
    exact mul_nonneg (mul_nonneg hK hY) hb0)
  have hKe : 1 ≤ Ke := by
    dsimp only [Ke]
    have hpow := one_le_pow₀ hJ (n := 3)
    linarith only [hpow]
  have hKc : 1 ≤ Kc := by
    dsimp only [Kc]
    have hpow := one_le_pow₀ hJ (n := 2)
    linarith only [hpow]
  have hCN : 1 ≤ CN := by
    have hn : 0 ≤ 100 * CD ^ 12 * Kc := by positivity
    dsimp only [CN]
    linarith only [hn]
  have hCM : 1 ≤ CM := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCD) (one_le_pow₀ hCs)
  have hCcommon : 1 ≤ Ccommon := one_le_mul_of_one_le_of_one_le hCB hCNtree
  have hlogCD : log CD = KD := log_exp KD
  have hlogCs : log Cs ≤ 8194 + KD := by
    dsimp only [Cs]
    rw [log_mul (by norm_num) (by positivity)]
    have hnum := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8194)
    have hinner := log_le_sub_one_of_pos (by positivity : 0 < KD + 1)
    linarith only [hnum, hinner]
  have hnum30 : log (1073741824 : ℝ) ≤ 30 := by
    have heq : (1073741824 : ℝ) = 2 ^ 30 := by norm_num
    rw [heq, log_pow]
    have htwo := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    linarith only [htwo]
  have hlogCt : log Ct ≤ 81971 + 34 * KD := by
    have hb := log_one_add_mul_pow_mul_pow_le 1073741824 CD Cs 24 10 (by norm_num) hCD hCs
    change log Ct ≤ _ at hb
    rw [hlogCD] at hb
    norm_num only [Nat.cast_ofNat] at hb
    linarith only [hb, hnum30, hlogCs]
  have hlogKe : log Ke ≤ 196608 + 3 * log J := by
    dsimp only [Ke]
    rw [log_mul (by norm_num) (by positivity), log_pow]
    have hnum := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 196608)
    norm_num only [Nat.cast_ofNat]
    linarith only [hnum]
  have hlogCost : log Kcost ≤ 278579 + 34 * KD + 3 * log J := by
    have hprod : Kcost ≤ Ct * Ke := max_le
      (le_mul_of_one_le_right (by linarith only [hCt]) hKe)
      (le_mul_of_one_le_left (by linarith only [hKe]) hCt)
    have hb := log_le_log (by linarith only [hKcost] : 0 < Kcost) hprod
    rw [log_mul (by positivity) (by positivity)] at hb
    linarith only [hb, hlogCt, hlogKe]
  have hb0 : b0 ≤ 278665 * X := by
    dsimp only [b0]
    rw [log_mul (by norm_num) (by positivity)]
    have hnum := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)
    dsimp only [X]
    linarith only [hnum, hlogCost, hKD, hlogg, hlogJ]
  have hlogCNtree : log CNtree ≤ 41020 * X := by
    have hb := log_one_add_mul_pow_mul_pow_le 32 CD Cs 12 5 (by norm_num) hCD hCs
    change log CNtree ≤ _ at hb
    rw [hlogCD] at hb
    have hnum := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)
    dsimp only [X]
    norm_num only [Nat.cast_ofNat] at hb
    linarith only [hb, hnum, hlogCs, hKD, hlogg, hlogJ]
  have hlogCN : log CN ≤ 615 * X := by
    have hb := log_one_add_mul_pow_mul_pow_le 600 CD J 12 2 (by norm_num) hCD hJ
    have heq : 1 + 600 * CD ^ 12 * J ^ 2 = CN := by dsimp only [CN, Kc]; ring
    rw [heq, hlogCD] at hb
    have hnum := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 600)
    dsimp only [X]
    norm_num only [Nat.cast_ofNat] at hb
    linarith only [hb, hnum, hKD, hlogg, hlogJ]
  have hlogCM : log CM ≤ 24591 * X := by
    have heq : log CM = 6 * KD + 3 * log Cs := by
      dsimp only [CM]
      rw [log_mul (by positivity) (by positivity), log_pow, log_pow, hlogCD]
      norm_num
    rw [heq]
    dsimp only [X]
    linarith only [hlogCs, hKD, hlogg, hlogJ]
  have hlogCB : log CB ≤ 278665 * K * Y * X := by
    have heq : log CB = K * Y * b0 := by dsimp only [CB, Y]; rw [log_exp]
    rw [heq]
    have hb := mul_le_mul_of_nonneg_left hb0 (mul_nonneg hK hY)
    nlinarith only [hb]
  have hlogPoly : log Cpoly ≤ 10000000 * (K + 1) * (Y + 1) * X := by
    have hb := log_one_add_mul_pow_mul_pow_le 1000000 (Ccommon * CN) CM 2 2
      (by norm_num) (one_le_mul_of_one_le_of_one_le hCcommon hCN) hCM
    change log Cpoly ≤ _ at hb
    rw [log_mul (by positivity) (by positivity),
      show log Ccommon = log CB + log CNtree from log_mul (by positivity) (by positivity)] at hb
    norm_num only [Nat.cast_ofNat] at hb
    have hnum := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1000000)
    have hKY : 0 ≤ K * Y := mul_nonneg hK hY
    have hKX : 0 ≤ K * X := mul_nonneg hK (by linarith only [hX])
    have hYX : 0 ≤ Y * X := mul_nonneg hY (by linarith only [hX])
    have hKYX : 0 ≤ K * Y * X := mul_nonneg hKY (by linarith only [hX])
    nlinarith only [hb, hnum, hlogCB, hlogCNtree, hlogCN, hlogCM, hX, hKX, hYX, hKYX]
  have hCpoly1 : 1 ≤ Cpoly := by
    have hn : 0 ≤ 1000000 * (Ccommon * CN) ^ 2 * CM ^ 2 := by positivity
    dsimp only [Cpoly]
    linarith only [hn]
  change log (max Cpoly 1) ≤ _
  rw [max_eq_left hCpoly1]
  convert hlogPoly using 1
  dsimp only [Y, X, a0, a1, J]
  ring


/-- The factored logarithmic coefficient estimate has a universal physical
scale majorant. Supporting the calibrated interleaved construction for ALVV,
arXiv:1602.08828v2, lines 1797–1817. -/
theorem interleaved_log_coefficient_bound_le
    (U u gamma g K KD CK : ℝ)
    (hU : 1 ≤ U) (hu : 0 ≤ u) (huU : u ≤ U)
    (hg : 0 < g) (hg1 : g ≤ 1) (hggamma : g ≤ gamma)
    (hlog : log (1 / g) ≤ U) (hK : 0 ≤ K) (hKD : 0 ≤ KD) (hCK : 0 ≤ CK)
    (hcount : KD ≤ CK * U ^ 7 / g) :
    10000000 * (K + 1) * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u + 1) *
      (1 + KD + log (1 / g) + log (1 + 1 / gamma)) ≤
      70000000 * (K + 1) * (CK + 4) * U ^ 10 / g ^ 2 := by
  have hCK4 : 0 ≤ CK + 4 := by linarith only [hCK]
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hgamma : 0 < gamma := hg.trans_le hggamma
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hrpow : (1 / g) ^ (1 / 4 : ℝ) ≤ 1 / g :=
    rpow_le_self_of_one_le hgInv (by norm_num)
  have hU3 : U ≤ U ^ 3 := by
    calc
      U = U ^ 1 := (pow_one _).symm
      _ ≤ _ := by gcongr; norm_num
  have hscale3 : 1 ≤ U ^ 3 / g :=
    (le_div_iff₀ hg).mpr (by simpa using hg1.trans (one_le_pow₀ hU))
  have hprofile : u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u + 1 ≤
      7 * (U ^ 3 / g) := by
    have hraw : u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u ≤ 6 * (U ^ 3 / g) := by
      calc
        _ ≤ U ^ 3 / g + 5 * (1 / g) * U ^ 3 := by
          gcongr
          exact huU.trans hU3
        _ = _ := by ring
    linarith only [hraw, hscale3]
  have hJ : 1 + 1 / gamma ≤ 2 * (1 / g) := by
    have hfrac := one_div_le_one_div_of_le hg hggamma
    linarith only [hfrac, hgInv]
  have hlogJ : log (1 + 1 / gamma) ≤ 1 + U := by
    have hb := log_le_log (by positivity : 0 < 1 + 1 / gamma) hJ
    rw [log_mul (by norm_num) (by positivity)] at hb
    have htwo := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hb, htwo, hlog]
  have hscale7 : 1 ≤ U ^ 7 / g :=
    (le_div_iff₀ hg).mpr (by simpa using hg1.trans (one_le_pow₀ hU))
  have hUscale7 : U ≤ U ^ 7 / g := by
    calc
      U ≤ U ^ 7 := by simpa using pow_le_pow_right₀ hU (by decide : 1 ≤ 7)
      _ ≤ U ^ 7 / g := (le_div_iff₀ hg).mpr (by nlinarith only [hg1, pow_nonneg hU0 7])
  have hsum : 1 + KD + log (1 / g) + log (1 + 1 / gamma) ≤
      (CK + 4) * (U ^ 7 / g) := by
    rw [mul_div_assoc] at hcount
    nlinarith only [hcount, hlog, hlogJ, hscale7, hUscale7]
  calc
    _ ≤ 10000000 * (K + 1) * (7 * (U ^ 3 / g)) * ((CK + 4) * (U ^ 7 / g)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hprofile (by positivity)
      · exact hsum
      · have hlogg : 0 ≤ log (1 / g) := log_nonneg hgInv
        have hlogJ0 : 0 ≤ log (1 + 1 / gamma) := log_nonneg (by linarith [one_div_pos.mpr hgamma])
        positivity
      · positivity
    _ = _ := by ring

end Real
