/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).

These are original integration proofs of the cited mathematical argument. No OpenAI Lean
proof text is copied or adapted here. The imported Gaussian construction retains its explicit
source and modification notices in Basic.lean and Covariance.lean.
-/
import QICLean.Probability.ComplexGaussian.SourceError
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# One global Gaussian law for positions and branch labels

All source positions and ordered ket/bra branch-label pairs are sampled once on a finite
nested product law. Fixing a deterministic label at each corrected position gives the actual
independent slot law by a measure-preserving coordinate projection. Covariance and expected
trace-error estimates therefore hold on this single global space. Their exponent counts
corrected positions, not branch-labelled coordinates.
For positive sample count, the coefficients are the actual centered replacement entries.
The integrability statements also cover zero sample count using the totalized coefficient API.

The source is *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
fresh samples and corrected-position expansion, `04-compression.tex:338--407,533--561`, at
OpenAI/math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The branch selector is fixed before sampling. Actual circuit expansion, branch identification,
and tensor-network assembly remain separate statements.
-/

noncomputable section

attribute [local instance 10000] Classical.propDecidable

open MeasureTheory
open scoped BigOperators ComplexConjugate Matrix Matrix.Norms.L2Operator

namespace QICLean.ComplexGaussian

open Classical in
private theorem measurePreserving_finsetRestrict {P : Type*} [Fintype P]
    {Ω : P → Type*} [∀ p, MeasurableSpace (Ω p)]
    (ν : (p : P) → Measure (Ω p)) [∀ p, IsProbabilityMeasure (ν p)] (S : Finset P) :
    MeasurePreserving (fun (ω : (p : P) → Ω p) (p : S) ↦ ω p)
      (Measure.pi ν) (Measure.pi (fun p : S ↦ ν p)) := by
  have hfst : MeasurePreserving Prod.fst
      ((Measure.pi (fun p : S ↦ ν p)).prod
        (Measure.pi (fun p : {p // p ∉ S} ↦ ν p)))
      (Measure.pi (fun p : S ↦ ν p)) := measurePreserving_fst
  have hsplit := measurePreserving_piEquivPiSubtypeProd ν (fun p ↦ p ∈ S)
  have hfintype : Subtype.fintype (fun p ↦ p ∈ S) = Finset.Subtype.fintype S :=
    Subsingleton.elim _ _
  rw [hfintype] at hsplit
  exact hfst.comp hsplit

private theorem integral_projection_of_integrable {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure X} {ν' : Measure Y} {f : X → Y} (hf : MeasurePreserving f ν ν')
    (g : Y → E) (hg : Integrable g ν') :
    (∫ x, g (f x) ∂ν) = ∫ y, g y ∂ν' := by
  have hgm : AEStronglyMeasurable g (ν.map f) := by
    simpa only [hf.map_eq] using hg.aestronglyMeasurable
  simpa only [hf.map_eq] using (integral_map hf.measurable.aemeasurable hgm).symm

variable {P : Type*} [Fintype P] {B : P → Type*} [∀ p, Fintype (B p)]
    {A C : (p : P) → B p → Type*}
    [∀ p b, Fintype (A p b)] [∀ p b, Fintype (C p b)]

/-
Provenance-ID: p09-qic-global-globalbranchlaw
Downstream declaration: QICLean.ComplexGaussian.globalBranchLaw
Source: September 24, 2026.
Label: eq:compression-subset-expansion
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L338-L379
-/

/-- A single law samples every position and every ordered branch-label pair.
Source: Theorem 5.2, fresh samples, `04-compression.tex:338--340`.
The label type may depend on the position; Schmidt supports may depend on both. -/
def globalBranchLaw (k : ℕ) (A C : (p : P) → B p → Type*)
    [∀ p b, Fintype (A p b)] [∀ p b, Fintype (C p b)] :
    Measure ((p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) :=
  Measure.pi (fun p ↦ independentDensityLaw k (A p) (C p))

/-
Provenance-ID: p09-qic-global-globalbranchlawisprobabilitymeasure
Downstream declaration: QICLean.ComplexGaussian.globalBranchLawIsProbabilityMeasure
Source: September 24, 2026.
Label: eq:compression-subset-expansion
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L338-L379
-/

/-- The nested global Gaussian law is a probability measure.
Source: Theorem 5.2, fresh samples, `04-compression.tex:338--340`. -/
instance globalBranchLawIsProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (globalBranchLaw k A C) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun p ↦ independentDensityLaw k (A p) (C p))))

/-
Provenance-ID: p09-qic-global-selectedbranchsamples
Downstream declaration: QICLean.ComplexGaussian.selectedBranchSamples
Source: September 24, 2026.
Label: eq:compression-subset-expansion
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L338-L379
-/

/-- Restrict global samples to corrected positions and fixed deterministic branch labels.
Source: Theorem 5.2, expansion by corrected positions, `04-compression.tex:342--379`.
This selector has no sample argument and chooses exactly one label at each selected position. -/
def selectedBranchSamples (k : ℕ) (S : Finset P) (σ : (p : S) → B p)
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) :
    (p : S) → Sample (Fin k × (A p (σ p) × C p (σ p))) :=
  fun p ↦ ω p (σ p)

/-
Provenance-ID: p09-qic-global-measurepreserving_selectedbranchsamples
Downstream declaration: QICLean.ComplexGaussian.measurePreserving_selectedBranchSamples
Source: September 24, 2026.
Label: eq:compression-subset-expansion
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L338-L379
-/

open Classical in
/-- The actual global coordinate projection has the checked independent corrected-slot law.
Source: Theorem 5.2, fresh samples and fixed choices, `04-compression.tex:338--379`.
No desired independence or pushforward identity is assumed. -/
theorem measurePreserving_selectedBranchSamples (k : ℕ) (S : Finset P)
    (σ : (p : S) → B p) :
    MeasurePreserving (selectedBranchSamples (A := A) (C := C) k S σ)
      (globalBranchLaw k A C)
      (independentDensityLaw k (fun p : S ↦ A p (σ p)) (fun p : S ↦ C p (σ p))) := by
  have hcoord := measurePreserving_pi
    (fun p : S ↦ independentDensityLaw k (A p) (C p))
    (fun p : S ↦ law (Fin k × (A p (σ p) × C p (σ p))))
    (fun p ↦ measurePreserving_eval (fun b ↦ law (Fin k × (A p b × C p b))) (σ p))
  exact hcoord.comp (measurePreserving_finsetRestrict
    (fun p ↦ independentDensityLaw k (A p) (C p)) S)

variable [∀ p b, DecidableEq (A p b)] [∀ p b, DecidableEq (C p b)]

/-
Provenance-ID: p09-qic-global-selectedbranchdensitycoefficient
Downstream declaration: QICLean.ComplexGaussian.selectedBranchDensityCoefficient
Source: September 24, 2026.
Label: eq:compression-product-covariance
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L369-L407
-/

/-- Actual selected correction coefficients, evaluated on the one global sample.
Source: Theorem 5.2, fixed choices and `eq:compression-product-covariance`,
`04-compression.tex:369--407`. The finite product ranges over corrected positions only. -/
def selectedBranchDensityCoefficient (k : ℕ) (S : Finset P) (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (i : (p : S) → A p (σ p) × A p (σ p))
    (l : (p : S) → C p (σ p) × C p (σ p))
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) : ℂ :=
  independentDensityCoefficient k lam mu i l (selectedBranchSamples k S σ ω)

/-
Provenance-ID: p09-qic-global-integrable_selectedbranchdensitycoefficient
Downstream declaration: QICLean.ComplexGaussian.integrable_selectedBranchDensityCoefficient
Source: September 24, 2026.
Label: eq:compression-product-covariance
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L369-L407
-/

open Classical in
/-- Selected Gaussian coefficients are integrable on the actual global law.
Source: Theorem 5.2, fixed choices, `04-compression.tex:369--407`. -/
theorem integrable_selectedBranchDensityCoefficient (k : ℕ) (S : Finset P)
    (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (i : (p : S) → A p (σ p) × A p (σ p))
    (l : (p : S) → C p (σ p) × C p (σ p)) :
    Integrable (selectedBranchDensityCoefficient k S σ lam mu i l) (globalBranchLaw k A C) :=
  (measurePreserving_selectedBranchSamples k S σ).integrable_comp_of_integrable
    (integrable_independentDensityCoefficient k lam mu i l)

/-
Provenance-ID: p09-qic-global-integrable_selectedbranchdensitycoefficient_mul_conj
Downstream declaration: QICLean.ComplexGaussian.integrable_selectedBranchDensityCoefficient_mul_conj
Source: September 24, 2026.
Label: eq:compression-product-covariance
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L369-L407
-/

open Classical in
/-- Selected coefficient conjugate products are integrable on the actual global law.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
theorem integrable_selectedBranchDensityCoefficient_mul_conj (k : ℕ) (S : Finset P)
    (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (i i' : (p : S) → A p (σ p) × A p (σ p))
    (l l' : (p : S) → C p (σ p) × C p (σ p)) :
    Integrable (fun ω ↦ selectedBranchDensityCoefficient k S σ lam mu i l ω *
      star (selectedBranchDensityCoefficient k S σ lam mu i' l' ω)) (globalBranchLaw k A C) :=
  (measurePreserving_selectedBranchSamples k S σ).integrable_comp_of_integrable
    (integrable_independentDensityCoefficient_mul_conj k lam mu i i' l l')

/-
Provenance-ID: p09-qic-global-integral_selectedbranchdensitycoefficient_mul_conj
Downstream declaration: QICLean.ComplexGaussian.integral_selectedBranchDensityCoefficient_mul_conj
Source: September 24, 2026.
Label: eq:compression-product-covariance
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L369-L407
-/

open Classical in
/-- Global-law covariance has inverse-sample exponent equal to the corrected-position count.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`.
All other positions and branch labels are integrated out; none contributes to this exponent. -/
theorem integral_selectedBranchDensityCoefficient_mul_conj (k : ℕ) (hk : 0 < k)
    (S : Finset P) (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (i i' : (p : S) → A p (σ p) × A p (σ p))
    (l l' : (p : S) → C p (σ p) × C p (σ p)) :
    (∫ ω, selectedBranchDensityCoefficient k S σ lam mu i l ω *
      star (selectedBranchDensityCoefficient k S σ lam mu i' l' ω)
      ∂globalBranchLaw k A C) =
      if i = i' ∧ l = l' then
        (((k : ℝ) ^ (-(S.card : ℝ)) *
          Real.sqrt (pairedProductProbability lam i * pairedProductProbability mu l) : ℝ) : ℂ)
      else 0 := by
  simp only [selectedBranchDensityCoefficient]
  rw [integral_projection_of_integrable (measurePreserving_selectedBranchSamples k S σ)
    (fun ω ↦ independentDensityCoefficient k lam mu i l ω *
      star (independentDensityCoefficient k lam mu i' l' ω))
    (integrable_independentDensityCoefficient_mul_conj k lam mu i i' l l')]
  simpa only [Fintype.card_coe] using
    integral_independentDensityCoefficient_mul_conj k hk lam mu hlam hmu i i' l l'

/-
Provenance-ID: p09-qic-global-integral_selectedbranchdensitycoefficient_eq_zero
Downstream declaration: QICLean.ComplexGaussian.integral_selectedBranchDensityCoefficient_eq_zero
Source: September 24, 2026.
Label: eq:compression-product-covariance
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L369-L407
-/

open Classical in
/-- Nonempty selected correction products are centered on the single global law.
Source: Theorem 5.2, centered corrections and fresh samples, `04-compression.tex:338--407`. -/
theorem integral_selectedBranchDensityCoefficient_eq_zero (k : ℕ) (S : Finset P)
    [Nonempty S] (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (i : (p : S) → A p (σ p) × A p (σ p))
    (l : (p : S) → C p (σ p) × C p (σ p)) :
    (∫ ω, selectedBranchDensityCoefficient k S σ lam mu i l ω ∂globalBranchLaw k A C) = 0 := by
  simp only [selectedBranchDensityCoefficient]
  rw [integral_projection_of_integrable (measurePreserving_selectedBranchSamples k S σ)
    (independentDensityCoefficient k lam mu i l)
    (integrable_independentDensityCoefficient k lam mu i l)]
  exact integral_independentDensityCoefficient_eq_zero k lam mu i l

variable {T U : Type*} [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U]

-- Match the canonical slot API on the finite tensor indices of selected positions.
local instance (S : Finset P) : DecidableEq S := Classical.decEq _

/-
Provenance-ID: p09-qic-global-integrable_rectangulartracenorm_selectedbranchsourceerror
Downstream declaration:
QICLean.ComplexGaussian.integrable_rectangularTraceNorm_selectedBranchSourceError
Source: September 24, 2026.
Label: eq:compression-one-choice
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L529-L561
-/

open Classical in
/-- The actual corrected-source trace error remains integrable on the global branch law.
Source: Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex:533--561`.
No separate coefficient measurability or sampled norm bound is assumed. -/
theorem integrable_rectangularTraceNorm_selectedBranchSourceError (k : ℕ) (S : Finset P)
    (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (((p : S) → C p (σ p) × C p (σ p)) × U)
      (((p : S) → A p (σ p) × A p (σ p)) × T) ℂ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError tau tau' O
        (fun b ↦ selectedBranchDensityCoefficient k S σ lam mu b.1 b.2 ω)))
      (globalBranchLaw k A C) :=
  (measurePreserving_selectedBranchSamples k S σ).integrable_comp_of_integrable
    (integrable_rectangularTraceNorm_gaussianSourceError k lam mu tau tau' O
      htau htau' htausum htau'sum)

/-
Provenance-ID: p09-qic-global-integral_rectangulartracenorm_selectedbranchsourceerror_le
Downstream declaration:
QICLean.ComplexGaussian.integral_rectangularTraceNorm_selectedBranchSourceError_le
Source: September 24, 2026.
Label: eq:compression-one-choice
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L529-L561
-/

open Classical in
/-- The one-choice trace error bound holds on a single global Gaussian law.
Source: Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex:533--561`.
The exponent is the number of corrected positions. Branch labels are fixed coordinates;
all normalized supports may differ and include zero weights. The transpose is ordinary. -/
theorem integral_rectangularTraceNorm_selectedBranchSourceError_le (k : ℕ) (hk : 0 < k)
    (S : Finset P) (σ : (p : S) → B p)
    (lam : (p : S) → A p (σ p) → ℝ) (mu : (p : S) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (hlamsum : ∀ p, ∑ a, lam p a = 1) (hmusum : ∀ p, ∑ c, mu p c = 1)
    (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (((p : S) → C p (σ p) × C p (σ p)) × U)
      (((p : S) → A p (σ p) × A p (σ p)) × T) ℂ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) (hO : ‖O‖ ≤ 1) :
    (∫ ω, Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError tau tau' O
        (fun b ↦ selectedBranchDensityCoefficient k S σ lam mu b.1 b.2 ω))
      ∂globalBranchLaw k A C) ≤ (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  simp only [selectedBranchDensityCoefficient]
  rw [integral_projection_of_integrable (measurePreserving_selectedBranchSamples k S σ)
    (fun ω ↦ Matrix.rectangularTraceNorm (ProbabilityTheory.weightedSourceError tau tau' O
      (fun b ↦ independentDensityCoefficient k lam mu b.1 b.2 ω)))
    (integrable_rectangularTraceNorm_gaussianSourceError k lam mu tau tau' O
      htau htau' htausum htau'sum)]
  simpa only [Fintype.card_coe] using
    integral_rectangularTraceNorm_gaussianSourceError_le k hk lam mu hlam hmu hlamsum hmusum
      tau tau' O htau htau' htausum htau'sum hO

end QICLean.ComplexGaussian
