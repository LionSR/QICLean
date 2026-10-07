/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binary-entropy bounds for excitation subsets

For `0 ≤ p ≤ 1 / 2`, the binomial coefficient at any `r ≤ p * k` is bounded by
`exp (k * Real.binEntropy p)`. Summing over admissible cardinalities gives at most
`(k + 1) * exp (k * Real.binEntropy p)` subsets of a set with `k` elements.
The zero-copy and zero-fraction cases are included.

These are the scalar counting estimates used before `comparator:inverse-compression`
in OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Section 7, lines 577–590 of `build/sections/07-comparators.tex`.
The parameter range `0 < τ < 1/2` is specified there at line 154; the present
bounds also include its endpoints.

The mathematical source is pinned to `openai/math` commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are original Lean proofs;
no upstream Lean proof text is reused.
-/

open scoped BigOperators

namespace Real

private theorem binomial_term_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {k r : ℕ} (hr : r ≤ k) :
    p ^ r * (1 - p) ^ (k - r) * (k.choose r : ℝ) ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun j => p ^ j * (1 - p) ^ (k - j) * (k.choose j : ℝ))
    (fun j _ => mul_nonneg (mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _))
      (Nat.cast_nonneg _)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  simpa only [← add_pow, show p + (1 - p) = 1 by ring, one_pow] using h

private theorem log_choose_le_mul_binEntropy_of_pos {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1 / 2)
    {k r : ℕ} (hr : (r : ℝ) ≤ p * k) :
    log (k.choose r : ℝ) ≤ k * binEntropy p := by
  have hrk : r ≤ k := by
    exact_mod_cast (hr.trans (show p * (k : ℝ) ≤ k by
      nlinarith [show (0 : ℝ) ≤ k by positivity]))
  have hterm := binomial_term_le_one hp.le (show p ≤ 1 by linarith) hrk
  have hq : 0 < 1 - p := by linarith
  have hc : (0 : ℝ) < k.choose r := by exact_mod_cast Nat.choose_pos hrk
  have hlog := log_le_log (mul_pos (mul_pos (pow_pos hp _) (pow_pos hq _)) hc) hterm
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_pow, log_one, Nat.cast_sub hrk] at hlog
  have hmul := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hr)
    (sub_nonpos.mpr (log_le_log hp (show p ≤ 1 - p by linarith)))
  simp only [binEntropy, log_inv]
  nlinarith

/-- The logarithm of an admissible binomial coefficient is bounded by binary entropy.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–578 (before `comparator:inverse-compression`).
Provenance-ID: excitationSubsetCounts8750-real.log_choose_le_mul_binEntropy.
-/
theorem log_choose_le_mul_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {k r : ℕ} (hr : (r : ℝ) ≤ p * k) :
    log (k.choose r : ℝ) ≤ k * binEntropy p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · have hr0 : r = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact_mod_cast (show (r : ℝ) ≤ 0 by simpa [← hp] using hr)
    simp [← hp, hr0]
  · exact log_choose_le_mul_binEntropy_of_pos hp hp1 hr

/-- Exponential form of the binary-entropy bound on an admissible binomial coefficient.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–578 (before `comparator:inverse-compression`).
Provenance-ID: excitationSubsetCounts8750-real.choose_le_exp_mul_binEntropy.
-/
theorem choose_le_exp_mul_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {k r : ℕ} (hr : (r : ℝ) ≤ p * k) :
    (k.choose r : ℝ) ≤ exp (k * binEntropy p) := by
  exact (le_exp_log _).trans (exp_le_exp.mpr (log_choose_le_mul_binEntropy hp hp1 hr))

/-- The sum of binomial coefficients over admissible excitation counts is bounded by
`(k + 1) * exp (k * binEntropy p)`.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–590 (before `comparator:inverse-compression`).
Provenance-ID: excitationSubsetCounts8750-real.sum_choose_le_mul_exp_binEntropy.
-/
theorem sum_choose_le_mul_exp_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (k : ℕ) :
    (∑ r ∈ (Finset.range (k + 1)).filter (fun r : ℕ => (r : ℝ) ≤ p * k),
      (k.choose r : ℝ)) ≤ ((k : ℝ) + 1) * exp (k * binEntropy p) := by
  have h := Finset.sum_le_sum (s := (Finset.range (k + 1)).filter
    (fun r : ℕ => (r : ℝ) ≤ p * k)) (fun r hr =>
      choose_le_exp_mul_binEntropy hp hp1 (Finset.mem_filter.mp hr).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have hc := Finset.card_filter_le (Finset.range (k + 1))
    (fun r : ℕ => (r : ℝ) ≤ p * k)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    exact_mod_cast (show _ ≤ k + 1 by simpa only [Finset.card_range] using hc))
    (exp_pos _).le)

end Real

namespace Finset

variable {α : Type*}

/-- Binary-entropy bound on the actual number of subsets with admissible cardinality.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–590 (before `comparator:inverse-compression`).
Provenance-ID: excitationSubsetCounts8750-finset.card_filter_powerset_le_mul_exp_binEntropy.
-/
theorem card_filter_powerset_le_mul_exp_binEntropy (s : Finset α)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ((s.powerset.filter (fun t : Finset α => (t.card : ℝ) ≤ p * s.card)).card : ℝ) ≤
      ((s.card : ℝ) + 1) * Real.exp (s.card * Real.binEntropy p) := by
  classical
  let I := (range (s.card + 1)).filter (fun r : ℕ => (r : ℝ) ≤ p * s.card)
  have hsub : s.powerset.filter (fun t : Finset α => (t.card : ℝ) ≤ p * s.card) ⊆
      I.biUnion (fun r => s.powersetCard r) := fun t ht =>
    mem_biUnion.mpr ⟨t.card, mem_filter.mpr ⟨mem_range.mpr
      (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp (mem_filter.mp ht).1))),
      (mem_filter.mp ht).2⟩,
      mem_powersetCard.mpr ⟨mem_powerset.mp (mem_filter.mp ht).1, rfl⟩⟩
  have hcard := (card_le_card hsub).trans
    (card_biUnion_le (s := I) (t := fun r => s.powersetCard r))
  simp only [card_powersetCard] at hcard
  have hc : ((s.powerset.filter (fun t : Finset α =>
      (t.card : ℝ) ≤ p * s.card)).card : ℝ) ≤
      ∑ r ∈ I, (s.card.choose r : ℝ) := by
    exact_mod_cast hcard
  exact hc.trans (Real.sum_choose_le_mul_exp_binEntropy hp hp1 s.card)

end Finset
