/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).

These are original integration proofs of the cited mathematical argument. No OpenAI Lean
proof text is copied or adapted here. The imported Gaussian construction retains its explicit
source and modification notices in Basic.lean and Covariance.lean.
-/
import QICLean.Probability.ComplexGaussian.IndependentSlots
import QICLean.Probability.WeightedSourceError

/-!
# Expected trace error of independent Gaussian source corrections

For fresh independent Gaussian source slots, we prove the expected rectangular trace-norm
bound `k^(-s/2)` for a fixed contraction between the full free registers. The block transpose
is ordinary transpose: it preserves each complex coefficient rather than conjugating it.
All ket, bra, and private Schmidt supports may differ; zero probability weights are allowed.

The source is *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
`eq:compression-block-second-moment`, `eq:compression-dimension-free`, and
`eq:compression-one-choice`, `04-compression.tex:403--538`, at OpenAI/math revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The coefficients and probability measure are the actual Gaussian constructions. No desired
covariance, moment, or measurability identity is assumed at the canonical endpoints.

The result concerns the separated contractions for one fixed deterministic branch choice.
It does not assert a distributed-circuit expansion or the network conclusion of Theorem 5.2.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate Matrix Matrix.Norms.L2Operator

namespace QICLean.ComplexGaussian

variable {S : Type*} [Fintype S] {A C : S → Type*}
    [∀ s, Fintype (A s)] [∀ s, Fintype (C s)]
    [∀ s, DecidableEq (A s)] [∀ s, DecidableEq (C s)]
    {T U : Type*} [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U]

open Classical in
private theorem integrable_source_coefficient_pair (k : ℕ)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (b c : ((s : S) → A s × A s) × ((s : S) → C s × C s)) :
    Integrable (fun ω ↦ independentDensityCoefficient k lam mu b.1 b.2 ω *
      conj (independentDensityCoefficient k lam mu c.1 c.2 ω)) (independentDensityLaw k A C) := by
  simpa only [Complex.star_def] using
    integrable_independentDensityCoefficient_mul_conj k lam mu b.1 c.1 b.2 c.2

open Classical in
private theorem source_coefficient_covariance (k : ℕ) (hk : 0 < k)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (hlam : ∀ s a, 0 ≤ lam s a) (hmu : ∀ s c, 0 ≤ mu s c)
    (b c : ((s : S) → A s × A s) × ((s : S) → C s × C s)) :
    (∫ ω, independentDensityCoefficient k lam mu b.1 b.2 ω *
      conj (independentDensityCoefficient k lam mu c.1 c.2 ω) ∂independentDensityLaw k A C) =
      if b = c then
        ((((k : ℝ) ^ (-(Fintype.card S : ℝ))) *
          Real.sqrt (pairedProductProbability lam b.1 * pairedProductProbability mu b.2) : ℝ) : ℂ)
      else 0 := by
  have h := integral_independentDensityCoefficient_mul_conj k hk lam mu hlam hmu
    b.1 c.1 b.2 c.2
  by_cases hbc : b = c
  · subst c
    simpa [Complex.star_def] using h
  · have hneq : ¬(b.1 = c.1 ∧ b.2 = c.2) := fun h ↦ hbc (Prod.ext h.1 h.2)
    simpa only [Complex.star_def, ite_eq_right hneq, ite_eq_right hbc] using h

open Classical in
/-- The trace norm of the actual Gaussian corrected-source error is integrable.
Source: Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex:403--538`.
Pair integrability from the actual Gaussian law supplies the required measurability; no
independent measurable-coefficient or finite-dimensional rank assumption is added. -/
theorem integrable_rectangularTraceNorm_gaussianSourceError (k : ℕ)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix ((((s : S) → C s × C s) × U)) ((((s : S) → A s × A s) × T)) ℂ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError tau tau' O
        (fun b ↦ independentDensityCoefficient k lam mu b.1 b.2 ω)))
      (independentDensityLaw k A C) := by
  exact ProbabilityTheory.integrable_rectangularTraceNorm_weightedSourceError tau tau' O
    (fun b ω ↦ independentDensityCoefficient k lam mu b.1 b.2 ω)
    (integrable_source_coefficient_pair k lam mu) htau htau' htausum htau'sum

open Classical in
/-- Exact quarter-weighted second moment for the actual Gaussian source corrections.
Source: Theorem 5.2, `eq:compression-block-second-moment`, `04-compression.tex:403--538`.
The full covariance is proved from the construction, not supplied as a hypothesis. -/
theorem integral_frobeniusNormSq_gaussianSourceQuarter_eq (k : ℕ) (hk : 0 < k)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (hlam : ∀ s a, 0 ≤ lam s a) (hmu : ∀ s c, 0 ≤ mu s c)
    (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix ((((s : S) → C s × C s) × U)) ((((s : S) → A s × A s) × T)) ℂ) :
    (∫ ω, Matrix.frobeniusNormSq
      (ProbabilityTheory.weightedSourceQuarter tau tau' O
        (fun b ↦ independentDensityCoefficient k lam mu b.1 b.2 ω))
      ∂independentDensityLaw k A C) =
      (k : ℝ) ^ (-(Fintype.card S : ℝ)) *
        ∑ b : ((s : S) → A s × A s) × ((s : S) → C s × C s),
          Real.sqrt (pairedProductProbability lam b.1 * pairedProductProbability mu b.2) *
            Matrix.frobeniusNormSq (Matrix.quarterWeighted tau' tau
              (ProbabilityTheory.sourceBlock O b.2 b.1)) := by
  exact ProbabilityTheory.integral_frobeniusNormSq_weightedSourceQuarter_eq
    (pairedProductProbability lam) (pairedProductProbability mu) tau tau' O
    (fun b ω ↦ independentDensityCoefficient k lam mu b.1 b.2 ω) _
    (integrable_source_coefficient_pair k lam mu)
    (source_coefficient_covariance k hk lam mu hlam hmu)

open Classical in
/-- Dimension-independent expected trace error of the actual Gaussian source replacements.
Source: Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex:403--538`.
The full free-input map is only assumed contractive. All probability supports may differ,
zero Schmidt weights are allowed, and the block transpose is ordinary full transpose.
There are no covariance, moment, or measurability hypotheses at this endpoint. -/
theorem integral_rectangularTraceNorm_gaussianSourceError_le (k : ℕ) (hk : 0 < k)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (hlam : ∀ s a, 0 ≤ lam s a) (hmu : ∀ s c, 0 ≤ mu s c)
    (hlamsum : ∀ s, ∑ a, lam s a = 1) (hmusum : ∀ s, ∑ c, mu s c = 1)
    (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix ((((s : S) → C s × C s) × U)) ((((s : S) → A s × A s) × T)) ℂ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) (hO : ‖O‖ ≤ 1) :
    (∫ ω, Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError tau tau' O
        (fun b ↦ independentDensityCoefficient k lam mu b.1 b.2 ω))
      ∂independentDensityLaw k A C) ≤ (k : ℝ) ^ (-(Fintype.card S : ℝ) / 2) := by
  have h := ProbabilityTheory.integral_rectangularTraceNorm_weightedSourceError_le
    (pairedProductProbability lam) (pairedProductProbability mu) tau tau' O
    (fun b ω ↦ independentDensityCoefficient k lam mu b.1 b.2 ω)
    ((k : ℝ) ^ (-(Fintype.card S : ℝ)))
    (pairedProductProbability_nonneg lam hlam) (pairedProductProbability_nonneg mu hmu)
    htau htau' (sum_pairedProductProbability_eq_one lam hlamsum)
    (sum_pairedProductProbability_eq_one mu hmusum) htausum htau'sum hO (by positivity)
    (integrable_source_coefficient_pair k lam mu)
    (source_coefficient_covariance k hk lam mu hlam hmu)
  have hsqrt : Real.sqrt ((k : ℝ) ^ (-(Fintype.card S : ℝ))) =
      (k : ℝ) ^ (-(Fintype.card S : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg k)]
    congr 1
    ring
  exact hsqrt ▸ h

end QICLean.ComplexGaussian
