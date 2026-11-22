/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The entropy cost of the information reset

A real inequality used at the end of the information reset: a unitary error
`δ ≤ C L^(-(2p + 10))` and a logarithmic dimension `N ≤ 1 + L² log q` give
`8 √δ N ≤ L^(-p)` once `L ≥ 8 √C (1 + log q)`.

Moved from TNLean, `TNLean/Lattice/RegionalReset.lean` at commit `e41c3b63`
(`reset_entropy_scalar`); its hypotheses `0 ≤ C` and `0 ≤ N` are not needed.

## Main results

* `Real.eight_mul_sqrt_mul_le_rpow_neg`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 612–630.
-/

namespace Real

/-- **The entropy cost of the reset.** If `1 ≤ L`, `8 √C (1 + l) ≤ L`, `δ ≤ C L^(-(2p + 10))`
and `N ≤ 1 + L² l`, then `8 √δ N ≤ L^(-p)`. Polynomial PEPS approximation,
`02-information.tex`, lines 612–630, with `l = log q` and `N = log (e q^{|R₀|})`. -/
theorem eight_mul_sqrt_mul_le_rpow_neg {C p l L δ N : ℝ} (hL1 : 1 ≤ L)
    (hL : 8 * √C * (1 + l) ≤ L) (hδ : δ ≤ C * L ^ (-(2 * p + 10))) (hN : N ≤ 1 + L ^ 2 * l) :
    8 * √δ * N ≤ L ^ (-p) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hRHS : 0 ≤ L ^ (-p) := by positivity
  by_cases hN0 : N < 0
  · nlinarith [Real.sqrt_nonneg δ]
  push Not at hN0
  by_cases hC : C < 0
  · have hδ0 : δ ≤ 0 := hδ.trans (mul_nonpos_of_nonpos_of_nonneg hC.le (by positivity))
    rw [Real.sqrt_eq_zero'.mpr hδ0]
    simpa using hRHS
  push Not at hC
  have hsqrt : √δ ≤ √C * L ^ (-(p + 5)) := by
    calc √δ ≤ √(C * L ^ (-(2 * p + 10))) := Real.sqrt_le_sqrt hδ
      _ = √C * L ^ (-(p + 5)) := by
        rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (L ^ _), ← Real.rpow_mul hL0.le]
        ring_nf
  have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
  have hN' : N ≤ L ^ 2 * (1 + l) := by nlinarith
  have hpow : L ^ (-(p + 5)) * L ^ 2 = L ^ (-(p + 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    norm_num
    ring_nf
  have hL3 : L ≤ L ^ 3 := by
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * L ^ 2 := by gcongr
      _ = L ^ 3 := by ring
  have hfinal : L ^ 3 * L ^ (-(p + 3)) = L ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    norm_num
  calc 8 * √δ * N ≤ 8 * (√C * L ^ (-(p + 5))) * (L ^ 2 * (1 + l)) := by gcongr
    _ = (8 * √C * (1 + l)) * (L ^ (-(p + 5)) * L ^ 2) := by ring
    _ = (8 * √C * (1 + l)) * L ^ (-(p + 3)) := by rw [hpow]
    _ ≤ L ^ 3 * L ^ (-(p + 3)) := by gcongr; exact hL.trans hL3
    _ = L ^ (-p) := hfinal

end Real
