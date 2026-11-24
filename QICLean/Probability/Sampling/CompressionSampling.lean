/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex
-/
import QICLean.Analysis.Real.SampleCount
import Mathlib.MeasureTheory.Integral.Average

/-!
# Sampling bounds for finite correction expansions

From an integrable expected-error estimate on a probability space, summed over the nonempty
subsets of a finite set of source positions, we obtain a deterministic realization whose error
is at most half the accuracy, for the positive integer sample count `binomialSampleCount`.

These are the sampling steps of *Polynomial PEPS approximation of gapped square-grid ground
states*, Theorem 5.2, `eq:compression-total-error` and the following paragraph,
`04-compression.tex`, lines 540--567, at OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The accuracy condition `0 < ε ≤ 1` is supplied there by `ε = L⁻ᵖ`, with `L ≥ 2` and `p > 0`.
The results here do not assert the Gaussian covariance, weighted trace-norm estimates,
distributed construction, or network-dimension conclusion of Theorem 5.2.

The Lean proofs in this file are newly written from the mathematical argument and Mathlib.
No OpenAI Lean source is copied or adapted.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace CompressionSampling

variable {ι Ω E : Type*} [DecidableEq ι]

section Expectation

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- Summing correction estimates indexed by nonempty subsets yields the total expected error.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`.
The correction estimates and the pointwise aggregate estimate are inputs from the preceding
Gaussian and weighted-norm arguments, not hypotheses replacing those arguments. -/
theorem integral_error_le_binomial (slots : Finset ι) (a : ℝ)
    (error : Ω → ℝ) (correction : Finset ι → Ω → ℝ)
    (herror : Integrable error μ)
    (hcorr : ∀ s ∈ slots.powerset.erase ∅, Integrable (correction s) μ)
    (hpoint : ∀ ω, error ω ≤ ∑ s ∈ slots.powerset.erase ∅, correction s ω)
    (hbound : ∀ s ∈ slots.powerset.erase ∅, ∫ ω, correction s ω ∂μ ≤ a ^ s.card) :
    ∫ ω, error ω ∂μ ≤ (1 + a) ^ slots.card - 1 := by
  calc
    ∫ ω, error ω ∂μ ≤ ∫ ω, ∑ s ∈ slots.powerset.erase ∅, correction s ω ∂μ :=
      integral_mono herror (integrable_finsetSum _ hcorr) hpoint
    _ = ∑ s ∈ slots.powerset.erase ∅, ∫ ω, correction s ω ∂μ :=
      integral_finsetSum _ hcorr
    _ ≤ ∑ s ∈ slots.powerset.erase ∅, a ^ s.card := Finset.sum_le_sum hbound
    _ = (1 + a) ^ slots.card - 1 := Finset.sum_powerset_erase_empty_pow_card slots a

/-- The expected norm of the actual correction sum obeys the binomial bound.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`.
This applies to any normed correction space once its preceding per-subset expected-norm
estimate is proved; it does not assume positivity of the corrections. -/
theorem integral_norm_sum_le_binomial [NormedAddCommGroup E]
    (slots : Finset ι) (a : ℝ) (correction : Finset ι → Ω → E)
    (hcorr : ∀ s ∈ slots.powerset.erase ∅, Integrable (correction s) μ)
    (hbound : ∀ s ∈ slots.powerset.erase ∅,
      ∫ ω, ‖correction s ω‖ ∂μ ≤ a ^ s.card) :
    ∫ ω, ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖ ∂μ ≤
      (1 + a) ^ slots.card - 1 := by
  exact integral_error_le_binomial slots a
    (fun ω ↦ ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖)
    (fun s ω ↦ ‖correction s ω‖) (integrable_finsetSum _ hcorr).norm
    (fun s hs ↦ (hcorr s hs).norm) (fun ω ↦ norm_sum_le _ _) hbound

/-- The expected norm of the correction sum has the source's exact sampling bound.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`.
The given real-power per-subset estimates are the outputs required from the preceding
Gaussian and weighted-norm arguments. -/
theorem integral_norm_sum_le_sampling_error [NormedAddCommGroup E]
    (slots : Finset ι) (Q k : ℝ) (hk : 0 < k)
    (correction : Finset ι → Ω → E)
    (hcorr : ∀ s ∈ slots.powerset.erase ∅, Integrable (correction s) μ)
    (hbound : ∀ s ∈ slots.powerset.erase ∅,
      ∫ ω, ‖correction s ω‖ ∂μ ≤ Q ^ s.card * k ^ (-(s.card : ℝ) / 2)) :
    ∫ ω, ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖ ∂μ ≤
      (1 + Q / Real.sqrt k) ^ slots.card - 1 := by
  apply integral_norm_sum_le_binomial slots (Q / Real.sqrt k) correction hcorr
  intro s hs
  simpa only [Real.rpow_neg_natCast_div_two k hk, div_pow, ← div_eq_mul_one_div] using hbound s hs

variable [IsProbabilityMeasure μ]

/-- The expected sampling bound gives a deterministic realization with the paper's
half-accuracy error. Source: Theorem 5.2, realization paragraph,
`04-compression.tex:558--567`. Integrability already supplies almost-everywhere measurability;
no assumed realization or additional sample-space nonemptiness hypothesis is used. -/
theorem exists_error_le_half_binomialSampleCount (N : ℕ) (Q ε : ℝ) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (error : Ω → ℝ) (herror : Integrable error μ)
    (hbound : ∫ ω, error ω ∂μ ≤
      (1 + Q / Real.sqrt (binomialSampleCount N Q ε)) ^ N - 1) :
    ∃ ω, error ω ≤ ε / 2 := by
  obtain ⟨ω, hω⟩ := exists_le_integral herror
  refine ⟨ω, ?_⟩
  have hquarter := one_add_div_sqrt_binomialSampleCount_pow_sub_one_le N Q ε hQ hε hε₁
  linarith

/-- A deterministic realization can also satisfy any almost-sure sample condition.
Source: Theorem 5.2, realization paragraph, `04-compression.tex:558--567`.
This permits selecting the error-bound realization outside any exceptional null set. -/
theorem exists_valid_error_le_half_binomialSampleCount (N : ℕ) (Q ε : ℝ) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (error : Ω → ℝ) (herror : Integrable error μ)
    (hbound : ∫ ω, error ω ∂μ ≤
      (1 + Q / Real.sqrt (binomialSampleCount N Q ε)) ^ N - 1)
    (valid : Ω → Prop) (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    ∃ ω, valid ω ∧ error ω ≤ ε / 2 := by
  obtain ⟨ω, hωvalid, hω⟩ := exists_notMem_null_le_integral herror (ae_iff.mp hvalid)
  refine ⟨ω, ?_, ?_⟩
  · simpa only [Set.mem_ofPred_eq, not_not] using hωvalid
  · have hquarter := one_add_div_sqrt_binomialSampleCount_pow_sub_one_le N Q ε hQ hε hε₁
    linarith

/-- Actual finite correction sums have a valid deterministic realization at half accuracy.
Source: Theorem 5.2, `eq:compression-total-error` and realization paragraph,
`04-compression.tex:540--567`.
This closes the sampling implication once the per-subset expected-norm estimates are proved;
it does not formalize their Gaussian or weighted trace-norm derivation. -/
theorem exists_valid_norm_sum_le_half_binomialSampleCount [NormedAddCommGroup E]
    (slots : Finset ι) (Q ε : ℝ) (hQ : 0 ≤ Q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (correction : Finset ι → Ω → E)
    (hcorr : ∀ s ∈ slots.powerset.erase ∅, Integrable (correction s) μ)
    (hbound : ∀ s ∈ slots.powerset.erase ∅,
      ∫ ω, ‖correction s ω‖ ∂μ ≤ Q ^ s.card *
        (binomialSampleCount slots.card Q ε : ℝ) ^ (-(s.card : ℝ) / 2))
    (valid : Ω → Prop) (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    ∃ ω, valid ω ∧ ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖ ≤ ε / 2 := by
  have hk : 0 < (binomialSampleCount slots.card Q ε : ℝ) := by
    exact_mod_cast (binomialSampleCount_bounds slots.card Q ε).1
  exact exists_valid_error_le_half_binomialSampleCount slots.card Q ε hQ hε hε₁
    (fun ω ↦ ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖)
    (integrable_finsetSum _ hcorr).norm
    (integral_norm_sum_le_sampling_error slots Q _ hk correction hcorr hbound) valid hvalid

end Expectation

end CompressionSampling
