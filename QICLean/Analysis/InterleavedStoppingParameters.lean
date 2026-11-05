/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InterleavedTrimmingIteration
import QICLean.Analysis.ViableNodeParameters

/-!
# Integer stopping scales for interleaved collective trimming

The upper integer logarithm leaves one final round after geometric success
crosses the square root of the contraction. The actual sample-overlap scale
and count budget pay the additive trimming loss at every preceding round.
These bounds support ALVV, arXiv:1602.08828v2, lines 1797–1805. They use a
larger integer count than the possibly nonintegral printed half-logarithm;
no printed running-time or adaptive sampling claim is made.
-/

namespace Real

/-- The actual count and sample scales satisfy every stopping condition,
including the penultimate-round crossing. Supporting ALVV,
arXiv:1602.08828v2, lines 1797–1805. -/
theorem interleaved_stopping_parameter_bounds (D s : ℕ) (hD : 2 ≤ D) (hs : 1 ≤ s) :
    let R := (D : ℝ) ^ 6
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    let beta := sqrt Delta
    let k := Nat.clog D (D ^ 2 * s)
    1 ≤ R ∧ 0 < a ∧ a ≤ 1 / 100 ∧ 0 < Delta ∧
      beta ≤ 1 / (100 * R) ∧ 4 * R * beta ≤ 1 ∧
      beta + a / 16 ≤ 1 / 200 ∧ 2 ≤ k ∧ beta ≤ R ^ (k - 1) * a := by
  intro R a Delta beta k
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hD0 : (0 : ℝ) < D := by linarith only [hDR]
  have hs0 : (0 : ℝ) < s := by linarith only [hsR]
  have hR64 : 64 ≤ R := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hDR 6
    norm_num at hp
    exact hp
  have hR0 : 0 < R := by linarith only [hR64]
  have hDpow : (4096 : ℝ) ≤ (D : ℝ) ^ 12 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hDR 12
    norm_num at hp
    exact hp
  have hsPow : (1 : ℝ) ≤ (s : ℝ) ^ 5 := one_le_pow₀ hsR
  have hprod : (4096 : ℝ) ≤ (D : ℝ) ^ 12 * (s : ℝ) ^ 5 := by
    simpa only [mul_one] using mul_le_mul hDpow hsPow (by norm_num) (by positivity)
  have ha : 0 < a := by dsimp only [a]; positivity
  have haSmall : a ≤ 1 / 100 := by
    dsimp only [a]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)).mpr
    nlinarith only [hprod]
  have hDelta : 0 < Delta := by dsimp only [Delta]; positivity
  have hbeta : beta ≤ 1 / (100 * R) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    dsimp only [Delta, R]
    field_simp
    nlinarith only [sq_nonneg ((D : ℝ) ^ 6)]
  have hbudget : 4 * R * beta ≤ 1 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 100 * R)).mp hbeta
    nlinarith only [hb]
  have hbetaSmall : beta ≤ 1 / 6400 := hbeta.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith only [hR64]))
  have hexit : beta + a / 16 ≤ 1 / 200 := by linarith only [hbetaSmall, haSmall]
  obtain ⟨hk, hlower, _hupper, _hdim⟩ := Nat.viable_node_power_bounds hD hs
  change 2 ≤ k at hk
  have hpower : (3 : ℝ) * s / 32 ≤ R ^ k * a := by
    have hpNat := Nat.pow_le_pow_left hlower 6
    have hp : ((D : ℝ) ^ 2 * (s : ℝ)) ^ 6 ≤ ((D : ℝ) ^ k) ^ 6 := by
      exact_mod_cast hpNat
    have hmul := mul_le_mul_of_nonneg_right hp ha.le
    have hleft : ((D : ℝ) ^ 2 * (s : ℝ)) ^ 6 * a = 3 * (s : ℝ) / 32 := by
      dsimp only [a]
      field_simp
    have hright : ((D : ℝ) ^ k) ^ 6 * a = R ^ k * a := by
      dsimp only [R]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 6]
    simpa only [hleft, hright] using hmul
  have hpred : R * (R ^ (k - 1) * a) = R ^ k * a := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hcross : beta ≤ R ^ (k - 1) * a := by
    have hbetaR : beta * R ≤ 1 / 100 := by
      have hb := (le_div_iff₀ (by positivity : 0 < 100 * R)).mp hbeta
      nlinarith only [hb]
    have hgrowth : R * (R ^ (k - 1) * a) ≥ 3 * (s : ℝ) / 32 := by
      rw [hpred]
      exact hpower
    nlinarith only [hbetaR, hgrowth, hsR, hR0]
  exact ⟨by linarith only [hR64], ha, haSmall, hDelta, hbeta,
    hbudget, hexit, hk, hcross⟩

/-- The calibrated recurrence reaches error `1/200` after the actual upper
integer logarithm, while every preceding error lies in `[0,1)`. This is a
scalar stopping statement supporting ALVV, arXiv:1602.08828v2,
lines 1797–1805; no sampling or running-time assertion is included. -/
theorem interleaved_trim_power_sequence_stops (D s : ℕ) (hD : 2 ≤ D) (hs : 1 ≤ s) :
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    let k := Nat.clog D (D ^ 2 * s)
    ∀ (u : ℕ → ℝ), u 0 = 1 - a →
      (∀ j, u (j + 1) = Delta * u j / (1 - u j + Delta * u j) + a / 16) →
      (∀ j, 0 ≤ u j ∧ u j < 1) ∧ u k ≤ 1 / 200 := by
  intro a Delta k u hu0 hstep
  obtain ⟨hR, ha, haSmall, hDelta, _hbetaBound, hbudget, hexit, hk, hcross⟩ :=
    interleaved_stopping_parameter_bounds D s hD hs
  exact interleaved_trim_sequence_stops a Delta (sqrt Delta) ((D : ℝ) ^ 6)
    ha haSmall hR hDelta.le (sqrt_nonneg _) (sq_sqrt hDelta.le)
    hbudget hexit u hu0 hstep k (by omega) hcross

end Real
