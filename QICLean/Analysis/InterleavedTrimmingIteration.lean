/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Tactic

/-!
# A stopping envelope for interleaved filtering and collective trimming

The success variable increases geometrically until it reaches the square root
of the complementary contraction. The following round then gives a small
error, despite the additive trimming loss. These scalar estimates support
ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670, and
the degenerate-ground-space induction, lines 1797–1805. They do not assert
an algorithmic running time or an adaptive sampling probability.
-/

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
