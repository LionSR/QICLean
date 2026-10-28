/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Ground-energy dependence of normalized power sampling

For `0 ≤ E0 ≤ N - 1`, put `C = (1 - E0 / N)⁻¹`. Then `1 ≤ C ≤ N` and
`log C ≤ E0 / (N - E0)`. At the natural-ceiling power
`m = ⌈(N - E0) / Δ * log Q⌉₊`, with `Δ > 0` and `Q ≥ 1`, these bounds give

`C^(2m) ≤ N² * exp (2 * E0 * log Q / Δ)`.

The ceiling costs the factor `C² ≤ N²`. The exponent retains the ground
energy. This is the normalization estimate in the published LVV supplementary
proof of Proposition 1, page 6, following its Methods theorem:
https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf,
DOI 10.1038/nphys3345. It supplies the energy-dependent sampling bound.
-/

namespace Real

/-- Positive-contraction normalization has an explicit logarithmic bound.
The local spectral ceiling gives `E0 ≤ N - 1`; LVV, published supplement, p. 6. -/
theorem power_sampling_normalization_bounds {N E0 : ℝ}
    (hE0 : 0 ≤ E0) (hEN : E0 ≤ N - 1) :
    let C := (1 - E0 / N)⁻¹
    1 ≤ C ∧ C ≤ N ∧ Real.log C ≤ E0 / (N - E0) := by
  intro C
  have hN : 0 < N := by linarith
  have ha : 1 ≤ N - E0 := by linarith
  have ha0 : 0 < N - E0 := lt_of_lt_of_le zero_lt_one ha
  have hC : C = N / (N - E0) := by
    dsimp [C]
    rw [show 1 - E0 / N = (N - E0) / N by field_simp]
    exact inv_div _ _
  have hCpos : 0 < C := by rw [hC]; exact div_pos hN ha0
  refine ⟨?_, ?_, ?_⟩
  · rw [hC, le_div_iff₀ ha0]
    linarith
  · rw [hC, div_le_iff₀ ha0]
    nlinarith
  · calc
      Real.log C ≤ C - 1 := Real.log_le_sub_one_of_pos hCpos
      _ = E0 / (N - E0) := by rw [hC]; field_simp; ring

/-- The normalized power retains the published ground-energy exponent.
LVV, published supplement to Proposition 1, p. 6. The natural ceiling costs
`C²`, bounded here by `N²`. -/
theorem power_sampling_normalization_pow_ceil_le {N E0 Δ Q : ℝ}
    (hE0 : 0 ≤ E0) (hEN : E0 ≤ N - 1) (hΔ : 0 < Δ) (hQ : 1 ≤ Q) :
    let C := (1 - E0 / N)⁻¹
    let m := ⌈(N - E0) / Δ * Real.log Q⌉₊
    C ^ (2 * m) ≤ N ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ) := by
  intro C m
  obtain ⟨hC1, hCN, hlog⟩ := power_sampling_normalization_bounds hE0 hEN
  change 1 ≤ C at hC1
  change C ≤ N at hCN
  change Real.log C ≤ E0 / (N - E0) at hlog
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hlog0 : 0 ≤ Real.log C := Real.log_nonneg hC1
  have ha0 : 0 < N - E0 := by linarith
  have hx : 0 ≤ (N - E0) / Δ * Real.log Q :=
    mul_nonneg (div_nonneg ha0.le hΔ.le) (Real.log_nonneg hQ)
  have hm : (m : ℝ) ≤ (N - E0) / Δ * Real.log Q + 1 := (Nat.ceil_lt_add_one hx).le
  have h1 := mul_le_mul_of_nonneg_right hm hlog0
  have h2 := mul_le_mul_of_nonneg_left hlog hx
  have hcancel : ((N - E0) / Δ * Real.log Q) * (E0 / (N - E0)) =
      E0 * Real.log Q / Δ := by field_simp
  rw [hcancel] at h2
  have hmain : ((2 * m : ℕ) : ℝ) * Real.log C ≤
      2 * Real.log C + 2 * E0 * Real.log Q / Δ := by
    calc
      _ = 2 * ((m : ℝ) * Real.log C) := by push_cast; ring
      _ ≤ 2 * (((N - E0) / Δ * Real.log Q + 1) * Real.log C) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * ((N - E0) / Δ * Real.log Q * Real.log C + Real.log C) := by ring
      _ ≤ 2 * (E0 * Real.log Q / Δ + Real.log C) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 (le_refl (Real.log C))) (by norm_num)
      _ = _ := by ring
  calc
    _ = Real.exp (((2 * m : ℕ) : ℝ) * Real.log C) := by
      rw [Real.exp_nat_mul, Real.exp_log hCpos]
    _ ≤ Real.exp (2 * Real.log C + 2 * E0 * Real.log Q / Δ) :=
      Real.exp_le_exp.mpr hmain
    _ = C ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ) := by
      have htwo : Real.exp (2 * Real.log C) = C ^ 2 := by
        simpa only [Nat.cast_ofNat, Real.exp_log hCpos] using Real.exp_nat_mul (Real.log C) 2
      rw [Real.exp_add, htwo]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hCpos.le hCN 2) (Real.exp_nonneg _)

end Real
