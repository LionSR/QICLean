/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic

/-!
# Sampling bounds for finite correction expansions

The nonempty subsets of a finite set of source positions contribute a binomial error bound.
We prove its exact sum, a positive integer sample count, and the existence of a deterministic
realization from an integrable expected-error estimate on a probability space.

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

/-
Provenance-ID: p09-qic-sampling-sum_nonempty_subsets_pow
Downstream declaration: CompressionSampling.sum_nonempty_subsets_pow
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-sum_nonempty_subsets_weight
Downstream declaration: CompressionSampling.sum_nonempty_subsets_weight
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-inverse_half_power
Downstream declaration: CompressionSampling.inverse_half_power
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-sum_nonempty_subsets_rpow
Downstream declaration: CompressionSampling.sum_nonempty_subsets_rpow
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-zero_slots_error
Downstream declaration: CompressionSampling.zero_slots_error
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-binomial_error_le_exp
Downstream declaration: CompressionSampling.binomial_error_le_exp
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-exp_eighth_sub_one_le_quarter
Downstream declaration: CompressionSampling.exp_eighth_sub_one_le_quarter
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-binomial_error_le_quarter
Downstream declaration: CompressionSampling.binomial_error_le_quarter
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-ratio_le_of_sample_count
Downstream declaration: CompressionSampling.ratio_le_of_sample_count
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-error_le_quarter_of_sample_count
Downstream declaration: CompressionSampling.error_le_quarter_of_sample_count
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-samplecount
Downstream declaration: CompressionSampling.sampleCount
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-samplecount_bounds
Downstream declaration: CompressionSampling.sampleCount_bounds
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-error_le_quarter_samplecount
Downstream declaration: CompressionSampling.error_le_quarter_sampleCount
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-integral_error_le_binomial
Downstream declaration: CompressionSampling.integral_error_le_binomial
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-integral_norm_sum_le_binomial
Downstream declaration: CompressionSampling.integral_norm_sum_le_binomial
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-integral_norm_sum_le_sampling_error
Downstream declaration: CompressionSampling.integral_norm_sum_le_sampling_error
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-exists_error_le_half_samplecount
Downstream declaration: CompressionSampling.exists_error_le_half_sampleCount
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-exists_valid_error_le_half_samplecount
Downstream declaration: CompressionSampling.exists_valid_error_le_half_sampleCount
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

/-
Provenance-ID: p09-qic-sampling-exists_valid_norm_sum_le_half_samplecount
Downstream declaration: CompressionSampling.exists_valid_norm_sum_le_half_sampleCount
Source: September 24, 2026; eq:compression-total-error;
independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L540-L567
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace CompressionSampling

variable {ι Ω E : Type*} [DecidableEq ι]

/-- The nonempty correction subsets have exactly the binomial total cost.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`.
The index set consists of source positions, not monomial labels. -/
theorem sum_nonempty_subsets_pow (slots : Finset ι) (a : ℝ) :
    (∑ s ∈ slots.powerset.erase ∅, a ^ s.card) = (1 + a) ^ slots.card - 1 := by
  have hsum : (∑ s ∈ slots.powerset, a ^ s.card) = (1 + a) ^ slots.card := by
    simpa [add_comm] using Finset.sum_pow_mul_eq_add_pow a (1 : ℝ) slots
  have herase := Finset.sum_erase_add slots.powerset (fun s ↦ a ^ s.card)
    (Finset.empty_mem_powerset slots)
  simp only [Finset.card_empty, pow_zero] at herase
  linarith

/-- Exact weighted correction sum in the square-root form used for sampling.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`. -/
theorem sum_nonempty_subsets_weight (slots : Finset ι) (Q k : ℝ) :
    (∑ s ∈ slots.powerset.erase ∅, Q ^ s.card / (Real.sqrt k) ^ s.card) =
      (1 + Q / Real.sqrt k) ^ slots.card - 1 := by
  simpa only [div_pow] using sum_nonempty_subsets_pow slots (Q / Real.sqrt k)

/-- The real-power expression in the paper is the same square-root weight for positive `k`.
Source: Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex:531--545`. -/
theorem inverse_half_power (k : ℝ) (hk : 0 < k) (n : ℕ) :
    k ^ (-(n : ℝ) / 2) = 1 / (Real.sqrt k) ^ n := by
  have hexp : -(n : ℝ) / 2 = -((1 / 2 : ℝ) * n) := by ring
  rw [hexp, Real.rpow_neg hk.le, Real.rpow_mul_natCast hk.le,
    ← Real.sqrt_eq_rpow, one_div]

/-- The source's real-power correction weights sum to the claimed total error.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`. -/
theorem sum_nonempty_subsets_rpow (slots : Finset ι) (Q k : ℝ) (hk : 0 < k) :
    (∑ s ∈ slots.powerset.erase ∅, Q ^ s.card * k ^ (-(s.card : ℝ) / 2)) =
      (1 + Q / Real.sqrt k) ^ slots.card - 1 := by
  simp_rw [inverse_half_power k hk, ← div_eq_mul_one_div]
  exact sum_nonempty_subsets_weight slots Q k

/-- With no source positions the exact sampling-error bound vanishes.
Source: Theorem 5.2, immediately after `eq:compression-total-error`,
`04-compression.tex:552`. -/
@[simp] theorem zero_slots_error (a : ℝ) : (1 + a) ^ (0 : ℕ) - 1 = 0 := by simp

/-- The binomial sampling bound is controlled by its exponential majorant.
Source: Theorem 5.2, realization paragraph, `04-compression.tex:553--565`. -/
theorem binomial_error_le_exp (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (1 + a) ^ N - 1 ≤ Real.exp ((N : ℝ) * a) - 1 := by
  have hpow : (1 + a) ^ N ≤ (Real.exp a) ^ N := by
    exact pow_le_pow_left₀ (by positivity)
      (by simpa [add_comm] using Real.add_one_le_exp a) N
  rw [← Real.exp_nat_mul] at hpow
  linarith

/-- The paper's quarter-accuracy exponential bound, for its accuracy range.
Source: Theorem 5.2, realization paragraph, `04-compression.tex:558--565`.
Here `0 < ε ≤ 1` follows from the source's target accuracy `ε = L⁻ᵖ`. -/
theorem exp_eighth_sub_one_le_quarter (ε : ℝ) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    Real.exp (ε / 8) - 1 ≤ ε / 4 := by
  have habs : |ε / 8| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hexp := Real.abs_exp_sub_one_le habs
  rw [abs_of_nonneg (by positivity : 0 ≤ ε / 8)] at hexp
  linarith [le_abs_self (Real.exp (ε / 8) - 1)]

/-- The prescribed ratio bounds the total error by a quarter of the accuracy.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex:546--565`. -/
theorem binomial_error_le_quarter (N : ℕ) (a ε : ℝ) (hN : 0 < N)
    (ha : 0 ≤ a) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hsmall : a ≤ ε / (8 * N)) :
    (1 + a) ^ N - 1 ≤ ε / 4 := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul : (N : ℝ) * a ≤ ε / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < (8 : ℝ) * N)).mp hsmall
    nlinarith
  calc
    (1 + a) ^ N - 1 ≤ Real.exp ((N : ℝ) * a) - 1 :=
      binomial_error_le_exp N a ha
    _ ≤ Real.exp (ε / 8) - 1 := by gcongr
    _ ≤ ε / 4 := exp_eighth_sub_one_le_quarter ε hε.le hε₁

/-- A square sample-count lower bound gives the ratio required by the paper.
Source: Theorem 5.2, sample choice, `04-compression.tex:553--558`.
Positive `k` is necessary for the sample average. -/
theorem ratio_le_of_sample_count (N k : ℕ) (Q ε : ℝ) (hN : 0 < N) (hk : 0 < k)
    (hε : 0 < ε) (hcount : (8 * N * Q / ε) ^ 2 ≤ (k : ℝ)) :
    Q / Real.sqrt k ≤ ε / (8 * N) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsqrt := Real.le_sqrt_of_sq_le hcount
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hkreal)]
  have hmul := (div_le_iff₀ hε).mp hsqrt
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (8 : ℝ) * N)).mpr
  nlinarith

/-- Any positive integer sample count above the required square gives quarter accuracy.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex:546--565`. The zero-slot case has exact zero error. -/
theorem error_le_quarter_of_sample_count (N k : ℕ) (Q ε : ℝ) (hk : 0 < k)
    (hQ : 0 ≤ Q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hcount : (8 * N * Q / ε) ^ 2 ≤ (k : ℝ)) :
    (1 + Q / Real.sqrt k) ^ N - 1 ≤ ε / 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [pow_zero, sub_self]
    positivity
  · exact binomial_error_le_quarter N _ ε hN (by positivity) hε hε₁
      (ratio_le_of_sample_count N k Q ε hN hk hε hcount)

/-- Positive sample count chosen only from the slot count, correction cost and accuracy.
Source: Theorem 5.2, sample choice, `04-compression.tex:553--558`.
Adding one handles `Q = 0` while keeping the same polynomial size bound. -/
def sampleCount (N : ℕ) (Q ε : ℝ) : ℕ := ⌈(8 * N * Q / ε) ^ 2⌉₊ + 1

/-- The explicit integer choice is positive, dominates the required square, and is bounded
by that square plus two. Source: Theorem 5.2, `04-compression.tex:553--558`. -/
theorem sampleCount_bounds (N : ℕ) (Q ε : ℝ) :
    0 < sampleCount N Q ε ∧
      (8 * N * Q / ε) ^ 2 ≤ (sampleCount N Q ε : ℝ) ∧
      (sampleCount N Q ε : ℝ) ≤ (8 * N * Q / ε) ^ 2 + 2 := by
  dsimp [sampleCount]
  refine ⟨by omega, ?_, ?_⟩
  · push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  · push_cast
    have h := Nat.ceil_lt_add_one (sq_nonneg (8 * N * Q / ε))
    linarith

/-- The explicit positive integer sample count achieves the quarter-error estimate.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex:546--565`. The zero-slot case requires no sampling estimate. -/
theorem error_le_quarter_sampleCount (N : ℕ) (Q ε : ℝ) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (1 + Q / Real.sqrt (sampleCount N Q ε)) ^ N - 1 ≤ ε / 4 := by
  obtain ⟨hk, hcount, _⟩ := sampleCount_bounds N Q ε
  exact error_le_quarter_of_sample_count N _ Q ε hk hQ hε hε₁ hcount

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
    _ = (1 + a) ^ slots.card - 1 := sum_nonempty_subsets_pow slots a

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
  simpa only [inverse_half_power k hk, div_pow, ← div_eq_mul_one_div] using hbound s hs

variable [IsProbabilityMeasure μ]

/-- The expected sampling bound gives a deterministic realization with the paper's
half-accuracy error. Source: Theorem 5.2, realization paragraph,
`04-compression.tex:558--567`. Integrability already supplies almost-everywhere measurability;
no assumed realization or additional sample-space nonemptiness hypothesis is used. -/
theorem exists_error_le_half_sampleCount (N : ℕ) (Q ε : ℝ) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (error : Ω → ℝ) (herror : Integrable error μ)
    (hbound : ∫ ω, error ω ∂μ ≤
      (1 + Q / Real.sqrt (sampleCount N Q ε)) ^ N - 1) :
    ∃ ω, error ω ≤ ε / 2 := by
  obtain ⟨ω, hω⟩ := exists_le_integral herror
  refine ⟨ω, ?_⟩
  have hquarter := error_le_quarter_sampleCount N Q ε hQ hε hε₁
  linarith

/-- A deterministic realization can also satisfy any almost-sure sample condition.
Source: Theorem 5.2, realization paragraph, `04-compression.tex:558--567`.
This permits selecting the error-bound realization outside any exceptional null set. -/
theorem exists_valid_error_le_half_sampleCount (N : ℕ) (Q ε : ℝ) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (error : Ω → ℝ) (herror : Integrable error μ)
    (hbound : ∫ ω, error ω ∂μ ≤
      (1 + Q / Real.sqrt (sampleCount N Q ε)) ^ N - 1)
    (valid : Ω → Prop) (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    ∃ ω, valid ω ∧ error ω ≤ ε / 2 := by
  obtain ⟨ω, hωvalid, hω⟩ := exists_notMem_null_le_integral herror (ae_iff.mp hvalid)
  refine ⟨ω, ?_, ?_⟩
  · simpa only [Set.mem_ofPred_eq, not_not] using hωvalid
  · have hquarter := error_le_quarter_sampleCount N Q ε hQ hε hε₁
    linarith

/-- Actual finite correction sums have a valid deterministic realization at half accuracy.
Source: Theorem 5.2, `eq:compression-total-error` and realization paragraph,
`04-compression.tex:540--567`.
This closes the sampling implication once the per-subset expected-norm estimates are proved;
it does not formalize their Gaussian or weighted trace-norm derivation. -/
theorem exists_valid_norm_sum_le_half_sampleCount [NormedAddCommGroup E]
    (slots : Finset ι) (Q ε : ℝ) (hQ : 0 ≤ Q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (correction : Finset ι → Ω → E)
    (hcorr : ∀ s ∈ slots.powerset.erase ∅, Integrable (correction s) μ)
    (hbound : ∀ s ∈ slots.powerset.erase ∅,
      ∫ ω, ‖correction s ω‖ ∂μ ≤ Q ^ s.card *
        (sampleCount slots.card Q ε : ℝ) ^ (-(s.card : ℝ) / 2))
    (valid : Ω → Prop) (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    ∃ ω, valid ω ∧ ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖ ≤ ε / 2 := by
  have hk : 0 < (sampleCount slots.card Q ε : ℝ) := by
    exact_mod_cast (sampleCount_bounds slots.card Q ε).1
  exact exists_valid_error_le_half_sampleCount slots.card Q ε hQ hε hε₁
    (fun ω ↦ ‖∑ s ∈ slots.powerset.erase ∅, correction s ω‖)
    (integrable_finsetSum _ hcorr).norm
    (integral_norm_sum_le_sampling_error slots Q _ hk correction hcorr hbound) valid hvalid

end Expectation

end CompressionSampling
