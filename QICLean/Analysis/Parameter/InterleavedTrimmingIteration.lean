/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import QICLean.Analysis.Parameter.ViableNodeParameters

/-!
# A stopping envelope for interleaved filtering and collective trimming

The success variable increases geometrically until it reaches the square root
of the complementary contraction. The following round then gives a small
error, despite the additive trimming loss. These scalar estimates support
ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670, and
the degenerate-ground-space induction, lines 1797–1805. They do not assert
an algorithmic running time or an adaptive sampling probability.

It also contains the following results.

* `Real.interleaved_stopping_parameter_bounds`, `Real.interleaved_trim_power_sequence_stops`:
  integer stopping scales for interleaved collective trimming.
-/

section InterleavedTrimmingIteration

namespace Real

/-- One normalized filter step, followed by an additive collective-trimming
loss, either multiplies the small success by `R` or reaches error `1/200`.
Supporting ALVV, arXiv:1602.08828v2, lines 1797–1805. -/
theorem interleaved_trim_step_bounds (a Delta beta R z : ℝ)
    (ha : 0 < a) (haSmall : a ≤ 1 / 100) (hR : 1 ≤ R)
    (hDelta : 0 ≤ Delta) (hbeta : 0 ≤ beta) (hbetaSq : beta ^ 2 = Delta)
    (hbudget : 4 * R * beta ≤ 1) (hexit : beta + a / 16 ≤ 1 / 200)
    (hz : 0 ≤ z) (hzUpper : z ≤ 1 - a) :
    let next := Delta * z / (1 - z + Delta * z) + a / 16
    0 ≤ next ∧ next ≤ 1 - a ∧
      (1 - z ≤ beta → R * (1 - z) ≤ 1 - next) ∧
      (beta ≤ 1 - z → next ≤ 1 / 200) := by
  intro next
  let b := 1 - z
  let den := b + Delta * z
  have hb : a ≤ b := by dsimp only [b]; linarith only [hzUpper]
  have hb0 : 0 < b := ha.trans_le hb
  have hden : 0 < den := add_pos_of_pos_of_nonneg hb0 (mul_nonneg hDelta hz)
  have hz1 : z ≤ 1 := by linarith only [hzUpper, ha]
  have hnext0 : 0 ≤ next :=
    add_nonneg (div_nonneg (mul_nonneg hDelta hz) hden.le) (by positivity)
  have hidentity : 1 - next = b / den - a / 16 := by
    dsimp only [next]
    change 1 - (Delta * z / den + a / 16) = b / den - a / 16
    field_simp
    dsimp only [den, b]
    ring
  have hlarge (hbBeta : beta ≤ b) : next ≤ 1 / 200 := by
    have hDeltaBound : Delta * z ≤ beta * den := by
      have hdz : Delta * z ≤ Delta := by simpa using mul_le_mul_of_nonneg_left hz1 hDelta
      have hbb : beta ^ 2 ≤ beta * b := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left hbBeta hbeta
      have hbd : beta * b ≤ beta * den :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hDelta hz)) hbeta
      exact hdz.trans ((hbetaSq.symm.le.trans hbb).trans hbd)
    have hratio : Delta * z / den ≤ beta := (div_le_iff₀ hden).mpr hDeltaBound
    dsimp only [next]
    linarith only [hratio, hexit]
  have hsmall (hbBeta : b ≤ beta) : R * b ≤ 1 - next := by
    have hbeta1 : beta ≤ 1 := by nlinarith only [hexit, ha]
    have hDeltaBeta : Delta ≤ beta := by nlinarith only [hbetaSq, hbeta, hbeta1]
    have hdenBeta : den ≤ 2 * beta := by
      have hdz : Delta * z ≤ Delta := by simpa using mul_le_mul_of_nonneg_left hz1 hDelta
      dsimp only [den]
      linarith only [hbBeta, hdz, hDeltaBeta]
    have hprod : 2 * R * den ≤ 1 :=
      (mul_le_mul_of_nonneg_left hdenBeta (by linarith only [hR])).trans
        (by nlinarith only [hbudget])
    have hgain : R * b + a / 16 ≤ 2 * R * b := by
      have hRb : b ≤ R * b := by simpa using mul_le_mul_of_nonneg_right hR hb0.le
      linarith only [hb, hRb, ha]
    have hnum : (R * b + a / 16) * den ≤ b := by
      calc
        _ ≤ (2 * R * b) * den := mul_le_mul_of_nonneg_right hgain hden.le
        _ = b * (2 * R * den) := by ring
        _ ≤ b * 1 := mul_le_mul_of_nonneg_left hprod hb0.le
        _ = b := mul_one b
    have hratio : R * b + a / 16 ≤ b / den := (le_div_iff₀ hden).mpr hnum
    rw [hidentity]
    linarith only [hratio]
  refine ⟨hnext0, ?_, hsmall, hlarge⟩
  by_cases hcase : b ≤ beta
  · have hsuccess := hsmall hcase
    have hRb : b ≤ R * b := by simpa using mul_le_mul_of_nonneg_right hR hb0.le
    linarith only [hsuccess, hRb, hb]
  · exact (hlarge (le_of_not_ge hcase)).trans (by linarith only [haSmall])

/-- The literal scalar recurrence stays below unit error and either has
already reached `1/200` or retains geometric success growth. Supporting
ALVV, arXiv:1602.08828v2, lines 1797–1805. -/
theorem interleaved_trim_sequence_bounds (a Delta beta R : ℝ)
    (ha : 0 < a) (haSmall : a ≤ 1 / 100) (hR : 1 ≤ R)
    (hDelta : 0 ≤ Delta) (hbeta : 0 ≤ beta) (hbetaSq : beta ^ 2 = Delta)
    (hbudget : 4 * R * beta ≤ 1) (hexit : beta + a / 16 ≤ 1 / 200)
    (u : ℕ → ℝ) (hu0 : u 0 = 1 - a)
    (hstep : ∀ j, u (j + 1) = Delta * u j / (1 - u j + Delta * u j) + a / 16) :
    ∀ j, 0 ≤ u j ∧ u j ≤ 1 - a ∧ (u j ≤ 1 / 200 ∨ R ^ j * a ≤ 1 - u j) := by
  intro j
  induction j with
  | zero =>
    rw [hu0]
    refine ⟨by linarith only [haSmall], le_rfl, Or.inr ?_⟩
    simp
  | succ j ih =>
    obtain ⟨hlo, hhi, hsmall, hlarge⟩ := interleaved_trim_step_bounds
      a Delta beta R (u j) ha haSmall hR hDelta hbeta hbetaSq hbudget hexit ih.1 ih.2.1
    rw [← hstep j] at hlo hhi hsmall hlarge
    refine ⟨hlo, hhi, ?_⟩
    by_cases hdone : u j ≤ 1 / 200
    · exact Or.inl (hlarge (by linarith only [hdone, hexit, ha]))
    by_cases hcross : beta ≤ 1 - u j
    · exact Or.inl (hlarge hcross)
    · right
      have hprev := ih.2.2.resolve_left hdone
      calc
        R ^ (j + 1) * a = R * (R ^ j * a) := by ring
        _ ≤ R * (1 - u j) := mul_le_mul_of_nonneg_left hprev (by linarith only [hR])
        _ ≤ 1 - u (j + 1) := hsmall (le_of_not_ge hcross)

/-- A geometric crossing by the penultimate round leaves one final round
for small error. Supporting ALVV, arXiv:1602.08828v2, lines 1797–1805. -/
theorem interleaved_trim_sequence_stops (a Delta beta R : ℝ)
    (ha : 0 < a) (haSmall : a ≤ 1 / 100) (hR : 1 ≤ R)
    (hDelta : 0 ≤ Delta) (hbeta : 0 ≤ beta) (hbetaSq : beta ^ 2 = Delta)
    (hbudget : 4 * R * beta ≤ 1) (hexit : beta + a / 16 ≤ 1 / 200)
    (u : ℕ → ℝ) (hu0 : u 0 = 1 - a)
    (hstep : ∀ j, u (j + 1) = Delta * u j / (1 - u j + Delta * u j) + a / 16)
    (n : ℕ) (hn : 1 ≤ n) (hcross : beta ≤ R ^ (n - 1) * a) :
    (∀ j, 0 ≤ u j ∧ u j < 1) ∧ u n ≤ 1 / 200 := by
  have hb := interleaved_trim_sequence_bounds a Delta beta R
    ha haSmall hR hDelta hbeta hbetaSq hbudget hexit u hu0 hstep
  refine ⟨fun j ↦ ⟨(hb j).1, by linarith only [(hb j).2.1, ha]⟩, ?_⟩
  have hprev := hb (n - 1)
  have hsuccess : beta ≤ 1 - u (n - 1) := by
    rcases hprev.2.2 with hdone | hgrowth
    · linarith only [hdone, hexit, ha]
    · exact hcross.trans hgrowth
  have hnext := (interleaved_trim_step_bounds a Delta beta R (u (n - 1))
    ha haSmall hR hDelta hbeta hbetaSq hbudget hexit hprev.1 hprev.2.1).2.2.2 hsuccess
  rw [← hstep (n - 1), Nat.sub_add_cancel hn] at hnext
  exact hnext

end Real

section InterleavedTrimmingParameters

/-!
# Reference and threshold budgets at small target overlap

A random subspace can have very small overlap with its target. The
weighted collective-trimming estimate then requires a reference error
quadratic in a guaranteed overlap, and a threshold error linear in that
overlap. These scalar bounds support the corrected interleaved assignment
in ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and the reference argument, lines 1801–1805. Physical construction and
parameter calibration are separate.
-/

namespace Real

/-- Quadratic reference accuracy and linear threshold error control the
actual weighted trimming expression uniformly, even when the incoming
filtered error is close to one. This supports the reference analysis of
ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and lines 1801–1805. The variable `f` is the normalized filtered error. -/
theorem weighted_reference_trim_error_le_filter_add
    {a f epsilon tau : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hepsilonBudget : epsilon ≤ a ^ 2 / 16384)
    (htau : 0 ≤ tau) (htauBudget : tau ≤ a / 256) :
    let theta := a / 64
    (1 + theta) * ((1 + theta) * f + (1 + 1 / theta) * epsilon + 2 * tau) +
      (1 + 1 / theta) * epsilon ≤ f + a / 16 := by
  intro theta
  have htheta : 0 < theta := by dsimp only [theta]; positivity
  have htheta1 : theta ≤ 1 / 64 := by dsimp only [theta]; linarith
  have haSq : a ^ 2 ≤ a := by nlinarith
  have hcoef : (1 + theta) ^ 2 ≤ 1 + 129 * a / 4096 := by
    dsimp only [theta]
    nlinarith
  have hfilter : (1 + theta) ^ 2 * f ≤ f + 129 * a / 4096 := by
    have h := mul_le_mul_of_nonneg_right hcoef hf0
    have h' := mul_nonneg (by positivity : 0 ≤ 129 * a / 4096) (sub_nonneg.mpr hf1)
    nlinarith
  have hepsilonCoef : (2 + theta) * (1 + 1 / theta) ≤ 128 / a + 4 := by
    have heq : (2 + theta) * (1 + 1 / theta) = 128 / a + 3 + theta := by
      dsimp only [theta]
      field_simp
      ring
    rw [heq]
    linarith
  have hepsilonTerm : (2 + theta) * (1 + 1 / theta) * epsilon ≤
      a / 128 + a / 4096 := by
    calc
      _ ≤ (128 / a + 4) * epsilon := mul_le_mul_of_nonneg_right hepsilonCoef hepsilon
      _ ≤ (128 / a + 4) * (a ^ 2 / 16384) :=
        mul_le_mul_of_nonneg_left hepsilonBudget (by positivity)
      _ = a / 128 + a ^ 2 / 4096 := by
        field_simp
        ring
      _ ≤ a / 128 + a / 4096 := by linarith
  have htauTerm : 2 * (1 + theta) * tau ≤ 65 * a / 8192 := by
    calc
      _ ≤ (65 / 32 : ℝ) * (a / 256) :=
        mul_le_mul (by linarith : 2 * (1 + theta) ≤ 65 / 32)
          htauBudget htau (by norm_num)
      _ = _ := by ring
  have hexpand :
      (1 + theta) * ((1 + theta) * f + (1 + 1 / theta) * epsilon + 2 * tau) +
        (1 + 1 / theta) * epsilon =
      (1 + theta) ^ 2 * f + (2 + theta) * (1 + 1 / theta) * epsilon +
        2 * (1 + theta) * tau := by ring
  rw [hexpand]
  linarith

end Real

end InterleavedTrimmingParameters

end InterleavedTrimmingIteration

section InterleavedStoppingParameters

/-!
## Integer stopping scales for interleaved collective trimming

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

end InterleavedStoppingParameters
