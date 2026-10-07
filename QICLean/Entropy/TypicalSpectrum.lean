/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProbabilityEntropy
import Mathlib.Algebra.BigOperators.Field

/-!
# Normalizing a typical part of a finite spectrum

Let `E` be a finite set of indices whose positive weights lie between
`exp (-S - w)` and `exp (-S + w)`, and let `z` be their total mass. After division
by `z`, the weights form a probability distribution. Both its entropy and the
logarithm of the cardinality of `E` differ from `S` by at most `w + |log z|`.
Weights outside `E` are unrestricted, so zero eigenvalues outside the selected
Schmidt indices cause no difficulty.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), equations `comparator:typical-set` and `comparator:typical-entropies`,
`07-comparators.tex`, lines 39–55, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:typical-set, comparator:typical-entropies.
Provenance-ID: 8753-qic-typical-01
Downstream declaration:
Entropy.normalizedRestriction
Provenance-ID: 8753-qic-typical-02
Downstream declaration:
Entropy.sum_normalizedRestriction
Provenance-ID: 8753-qic-typical-03
Downstream declaration:
Entropy.normalizedRestriction_pos
Provenance-ID: 8753-qic-typical-04
Downstream declaration:
Entropy.log_card_typical_centered
Provenance-ID: 8753-qic-typical-05
Downstream declaration:
Entropy.entropy_normalizedRestriction_typical_centered
Provenance-ID: 8753-qic-typical-06
Downstream declaration:
Entropy.typicalSpectrum_entropy_bounds
-/

open scoped BigOperators

namespace Entropy

variable {ι : Type*}

/-- A finite family restricted to `E` and divided by its mass.
OpenAI area-law manuscript, `comparator:typical-set`. -/
noncomputable def normalizedRestriction (p : ι → ℝ) (E : Finset ι) (i : E) : ℝ :=
  p i / ∑ j ∈ E, p j

/-- Restricting to a set of nonzero mass and normalizing gives total weight one. -/
theorem sum_normalizedRestriction {p : ι → ℝ} {E : Finset ι}
    (hz : (∑ j ∈ E, p j) ≠ 0) : ∑ i : E, normalizedRestriction p E i = 1 := by
  classical
  simp only [normalizedRestriction, ← Finset.sum_div]
  rw [Finset.sum_coe_sort]
  exact div_self hz

/-- The number of typical indices has logarithm within `w` of `S + log z`.
OpenAI area-law manuscript, `comparator:typical-entropies`. -/
theorem log_card_typical_centered {p : ι → ℝ} {E : Finset ι} {S w : ℝ}
    (hz : 0 < ∑ i ∈ E, p i)
    (hE : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |Real.log (E.card : ℝ) - S - Real.log (∑ i ∈ E, p i)| ≤ w := by
  classical
  have hne : E.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hz
  have hc : (0 : ℝ) < E.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hlo := Finset.sum_le_sum fun i hi ↦ (hE i hi).1
  have hhi := Finset.sum_le_sum fun i hi ↦ (hE i hi).2
  simp only [Finset.sum_const, nsmul_eq_mul] at hlo hhi
  have hloglo := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlo
  have hloghi := Real.log_le_log hz hhi
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hloglo hloghi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The normalized restriction of positive selected weights is positive. -/
theorem normalizedRestriction_pos {p : ι → ℝ} {E : Finset ι}
    (hz : 0 < ∑ j ∈ E, p j) {i : E} (hi : 0 < p i) :
    0 < normalizedRestriction p E i := div_pos hi hz

/-- The entropy of the normalized typical spectrum is within `w` of `S + log z`.
OpenAI area-law manuscript, `comparator:typical-entropies`. -/
theorem entropy_normalizedRestriction_typical_centered {p : ι → ℝ} {E : Finset ι}
    {S w : ℝ} (hz : 0 < ∑ i ∈ E, p i)
    (hE : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |probabilityEntropy (normalizedRestriction p E) - S -
      Real.log (∑ i ∈ E, p i)| ≤ w := by
  classical
  have hp (i : E) : 0 < p i := (Real.exp_pos _).trans_le (hE i i.property).1
  have hpoint (i : E) :
      S - w + Real.log (∑ j ∈ E, p j) ≤
          -Real.log (normalizedRestriction p E i) ∧
        -Real.log (normalizedRestriction p E i) ≤ S + w + Real.log (∑ j ∈ E, p j) := by
    have hl := Real.log_le_log (Real.exp_pos _) (hE i i.property).1
    have hu := Real.log_le_log (hp i) (hE i i.property).2
    rw [Real.log_exp] at hl hu
    rw [normalizedRestriction, Real.log_div (hp i).ne' hz.ne']
    constructor <;> linarith
  have hlo := Finset.sum_le_sum (s := Finset.univ) fun (i : E) _ ↦
    mul_le_mul_of_nonneg_left (hpoint i).1 (normalizedRestriction_pos hz (hp i)).le
  have hhi := Finset.sum_le_sum (s := Finset.univ) fun (i : E) _ ↦
    mul_le_mul_of_nonneg_left (hpoint i).2 (normalizedRestriction_pos hz (hp i)).le
  have hsum := sum_normalizedRestriction hz.ne'
  have hent : probabilityEntropy (normalizedRestriction p E) =
      ∑ i : E, normalizedRestriction p E i * -Real.log (normalizedRestriction p E i) := by
    simp only [probabilityEntropy, Real.negMulLog, mul_neg, neg_mul]
  rw [← hent, ← Finset.sum_mul, hsum, one_mul] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The logarithmic cardinality and normalized entropy estimates for a typical
Schmidt set. OpenAI area-law manuscript, `comparator:typical-entropies`.
Only the selected weights occur in the hypotheses; no strict positivity of the
whole marginal spectrum is required. -/
theorem typicalSpectrum_entropy_bounds {p : ι → ℝ} {E : Finset ι} {S w : ℝ}
    (hz : 0 < ∑ i ∈ E, p i)
    (hE : ∀ i ∈ E, Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) :
    |Real.log (E.card : ℝ) - S| ≤ w + |Real.log (∑ i ∈ E, p i)| ∧
      |probabilityEntropy (normalizedRestriction p E) - S| ≤
        w + |Real.log (∑ i ∈ E, p i)| := by
  have htriangle (x z : ℝ) (h : |x - S - z| ≤ w) : |x - S| ≤ w + |z| := by
    calc |x - S| = |(x - S - z) + z| := by congr 1; ring
      _ ≤ |x - S - z| + |z| := abs_add_le _ _
      _ ≤ w + |z| := by linarith
  exact ⟨htriangle _ _ (log_card_typical_centered hz hE),
    htriangle _ _ (entropy_normalizedRestriction_typical_centered hz hE)⟩

end Entropy
