/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BellOverlapLogBound

/-!
# The logarithmic rate from a sharp selected-sector bound

The exact pin coefficient, the supplied sector mass and the terminal-weighted
sharp exponential estimate give the negative-logarithmic physical rate. The
error is bounded by the existing Bell overlap remainder, uniformly for inverse
exponents in the indicated compact interval. Its already proved limit applies
with dimensions and the band count fixed before the replica limit.

This is a scalar implication. The physical application must derive its finite
norm estimate and mass bound for the same selected state and label sequence.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 383--418,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

private theorem sharp_bell_log_error_le (d G k : ℕ) (C s : ℝ)
    (hC : 0 ≤ C) (hs : 2 * s ∈ Set.Icc (0 : ℝ) 1) :
    (1 + 2 * s * G) * (Real.log 2 + (d : ℝ) ^ 2 * Real.log ((k : ℝ) + 1)) +
        2 * s * G * C * Real.log ((k : ℝ) + 2) ≤
      Real.log 4 + ((d : ℝ) ^ 2 + (C + (d : ℝ) ^ 2 + 1) * G) *
        Real.log ((k : ℝ) + 2) := by
  have hG : (0 : ℝ) ≤ G := Nat.cast_nonneg G
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogk : 0 ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_nonneg (by linarith only [hk])
  have hshift : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith only [hk])
  have htwo : Real.log 2 ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_left hk)
  have hp : 0 ≤ 1 + 2 * s * G :=
    add_nonneg zero_le_one (mul_nonneg hs.1 hG)
  have hps : 1 + 2 * s * G ≤ 1 + (G : ℝ) := by
    simpa only [one_mul] using
      _root_.add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_right hs.2 hG)
  have hfirst := mul_le_mul_of_nonneg_left
    (_root_.add_le_add (le_refl (Real.log 2))
      (mul_le_mul_of_nonneg_left hshift (sq_nonneg (d : ℝ)))) hp
  have hsecond := mul_le_mul_of_nonneg_right hps
    (add_nonneg hlog2 (mul_nonneg (sq_nonneg (d : ℝ)) hlogk))
  have hthird := mul_le_mul_of_nonneg_right hs.2
    (mul_nonneg (mul_nonneg hG hC) hlogk)
  have hfourth := mul_le_mul_of_nonneg_left htwo hG
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog4]
  nlinarith only [hfirst, hsecond, hthird, hfourth, hlog2]

/-- The sharp sector estimate gives the physical negative-log rate with the
original entropy sum and exact selected-mass costs. Positivity of the squared
norm is derived, and the error is an instance of the already vanishing Bell
overlap remainder. Source: area-law manuscript, `07-comparators.tex`,
`comparator:sharp-upper`, lines 383--418. -/
theorem neg_log_div_le_of_sharp_bell_bound (d G k : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (z C K a S s q r : ℝ) (hz : 0 < z) (hC : 0 ≤ C)
    (hs : 2 * s ∈ Set.Icc (0 : ℝ) 1)
    (hmass : 1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (d ^ 2))) ≤ q)
    (hbound : (z / (d : ℝ) ^ 2) ^ k * q ^ (1 + 2 * s * G) *
        Real.exp (-2 * s * ((k : ℝ) * a * S +
          (G : ℝ) * (12 * K * k * a ^ 2 - k * Real.log z +
            C * Real.log ((k : ℝ) + 2)))) ≤ r) :
    0 < r ∧ -Real.log r / (k : ℝ) ≤
      2 * Real.log (d : ℝ) - Real.log z + 2 * s * a * S +
        24 * s * G * K * a ^ 2 - 2 * s * G * Real.log z +
          bellOverlapRemainder d (C + (d : ℝ) ^ 2 + 1) G k := by
  have hmasspos : 0 < 1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (d ^ 2))) := by
    positivity
  have hq : 0 < q := hmasspos.trans_le hmass
  have hleft : 0 < (z / (d : ℝ) ^ 2) ^ k * q ^ (1 + 2 * s * G) *
      Real.exp (-2 * s * ((k : ℝ) * a * S +
        (G : ℝ) * (12 * K * k * a ^ 2 - k * Real.log z +
          C * Real.log ((k : ℝ) + 2)))) := by
    positivity
  have hr : 0 < r := hleft.trans_le hbound
  have hlog := Real.log_le_log hleft hbound
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
    Real.log_rpow, Real.log_exp, Nat.cast_ofNat] at hlog
  have hmasslog := Real.log_le_log hmasspos hmass
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_one, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hmasslog
  have hqlog : -Real.log q ≤ Real.log 2 +
      (d : ℝ) ^ 2 * Real.log ((k : ℝ) + 1) := by
    linarith only [hmasslog]
  have hcost := mul_le_mul_of_nonneg_left hqlog
    (add_nonneg zero_le_one (mul_nonneg hs.1 (Nat.cast_nonneg G)))
  have herr := sharp_bell_log_error_le d G k C s hC hs
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hk)
  refine ⟨hr, (div_le_iff₀ hkpos).2 ?_⟩
  rw [bellOverlapRemainder, add_mul, div_mul_cancel₀ _ hkpos.ne']
  nlinarith only [hlog, hcost, herr]

end Real
