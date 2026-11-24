/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.Samples
import QICLean.Probability.Gaussian.GlobalBranchLaw
import QICLean.Probability.Gaussian.ProductSourceTransport
import QICLean.Probability.Concentration.MatrixTraceNormIntegrability

/-!
# The Gaussian law of the sources of a source circuit

One law samples every source position and every ordered pair of labels of its gate
independently (`SourceCircuit.sourceGaussianLaw`): the samples are drawn before any corrected
set, affected set or partial expansion is chosen. Each fixed position and pair of labels has the
standard Gaussian law (`measurePreserving_sourceGaussian_eval`), and fixed labels at a set of
positions select independent samples (`measurePreserving_selected_sourceGaussian`).

With Schmidt frames representing the source vectors, the sampled source matrices are integrable
and unbiased (`integral_sampledSourceMatrix`, `exists_unbiased_sampledSourceMatrix`), the
corrections have mean zero (`integral_sourceGaussianCorrection`), the products of their entries
over a set `S` of positions have diagonal covariance with exponent `|S|`
(`integral_sourceCorrection_product_mul_conj`) and a nonempty product has mean zero
(`integral_sourceCorrection_product_eq_zero`); every matrix combination of these products has
integrable trace norm (`integrable_rectangularTraceNorm_sourceCorrectionSum`).

This module takes laws and integrals, and is one of the modules of
`Circuit/Party/Compression/SourceSampling` allowed to import `QICLean.Probability`.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.sourceGaussianLaw`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.measurePreserving_sourceGaussian_eval`,
  `QuantumCircuit.Party.SourceCircuit.measurePreserving_selected_sourceGaussian`.
* `QuantumCircuit.Party.SourceCircuit.integral_sampledSourceMatrix`,
  `QuantumCircuit.Party.SourceCircuit.exists_unbiased_sampledSourceMatrix`,
  `QuantumCircuit.Party.SourceCircuit.integral_sourceGaussianCorrection`.
* `QuantumCircuit.Party.SourceCircuit.integral_sourceCorrection_product_mul_conj`,
  `QuantumCircuit.Party.SourceCircuit.integral_sourceCorrection_product_eq_zero`,
  `QuantumCircuit.Party.SourceCircuit.integrable_rectangularTraceNorm_sourceCorrectionSum`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 279–407 (equations `eq:compression-random-source`,
  `eq:compression-product-covariance`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceGaussianLaw.lean` (the law),
`SourceGaussianDensity.lean` (the integral), `SourceGaussianCoefficients.lean` and
`GaussianSourceIntegrability.lean` (Apache-2.0). Changes: the frames have the slot bases as rows
and represent the source vectors themselves.
-/

open MeasureTheory Matrix ProductSource QICLean.ComplexGaussian
open scoped ComplexConjugate Matrix.Norms.Elementwise

namespace QuantumCircuit.Party

namespace SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

-- Matrix's norm is inherited from finite function spaces; expose its continuous enorm directly.
noncomputable local instance {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

/-- **One law for all source positions and ordered pairs of labels**, independent across them.
Source: Theorem 5.2, `04-compression.tex`, lines 338–340. -/
noncomputable def sourceGaussianLaw (w : SourceCircuit X Y) (k : ℕ) :
    Measure (SourceGaussianSamples w k) :=
  globalBranchLaw k
    (fun (e : w.sourceLocations) (_ : w.branchLabels e.1 × w.branchLabels e.1) ↦
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
    (fun (e : w.sourceLocations) (_ : w.branchLabels e.1 × w.branchLabels e.1) ↦
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2))

/-- The law of the sources has total mass one. -/
instance sourceGaussianLawIsProbabilityMeasure (w : SourceCircuit X Y) (k : ℕ) :
    IsProbabilityMeasure (sourceGaussianLaw w k) :=
  inferInstanceAs (IsProbabilityMeasure (globalBranchLaw k _ _))

/-- **The sample at a fixed position and pair of labels has the standard Gaussian law**; no
label is chosen as a function of the sample. Source: Theorem 5.2, `04-compression.tex`,
lines 338–340. -/
theorem measurePreserving_sourceGaussian_eval (w : SourceCircuit X Y) (k : ℕ)
    (e : w.sourceLocations) (ξ ζ : w.branchLabels e.1) :
    MeasurePreserving (fun ω : SourceGaussianSamples w k ↦ ω e (ξ, ζ)) (sourceGaussianLaw w k)
      (law (Fin k × (Fin (min (w.sourceDims e).1 (w.sourceDims e).2) ×
        Fin (min (w.sourceDims e).1 (w.sourceDims e).2)))) :=
  (measurePreserving_eval (fun _ : w.branchLabels e.1 × w.branchLabels e.1 ↦
    law (Fin k × (Fin (min (w.sourceDims e).1 (w.sourceDims e).2) ×
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2)))) (ξ, ζ)).comp
    (measurePreserving_eval (fun e : w.sourceLocations ↦ independentDensityLaw k
      (fun _ : w.branchLabels e.1 × w.branchLabels e.1 ↦
        Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
      (fun _ : w.branchLabels e.1 × w.branchLabels e.1 ↦
        Fin (min (w.sourceDims e).1 (w.sourceDims e).2))) e)

/-- **Fixed labels at a set of positions select independent samples**; the other positions and
labels are integrated out. Source: Theorem 5.2, `04-compression.tex`, lines 338–383. -/
theorem measurePreserving_selected_sourceGaussian (w : SourceCircuit X Y) (k : ℕ)
    (S : Finset w.sourceLocations) (ξ ζ : ∀ e : S, w.branchLabels e.1.1) :
    MeasurePreserving (fun (ω : SourceGaussianSamples w k) (e : S) ↦ ω e.1 (ξ e, ζ e))
      (sourceGaussianLaw w k)
      (independentDensityLaw k
        (fun e : S ↦ Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2))
        (fun e : S ↦ Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2))) :=
  measurePreserving_selectedBranchSamples
    (B := fun e : w.sourceLocations ↦ w.branchLabels e.1 × w.branchLabels e.1)
    (A := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
    (C := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
    k S (fun e ↦ (ξ e, ζ e))

section Frames

variable (w : SourceCircuit X Y) (k : ℕ)
  (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- Every sampled source matrix is integrable for the law of the sources. Source: Theorem 5.2,
`04-compression.tex`, lines 279–340. -/
theorem integrable_sampledSourceMatrix (hk : 0 < k) (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (e : w.sourceLocations) (ξ ζ : w.branchLabels e.1) :
    Integrable (sampledSourceMatrix w k lam E F e ξ ζ) (sourceGaussianLaw w k) :=
  (measurePreserving_sourceGaussian_eval w k e ξ ζ).integrable_comp_of_integrable
    (integrable_ambientSampledSource k hk (lam e ξ) (lam e ζ) (hnonneg e ξ) (hnonneg e ζ)
      (E e ξ) (F e ξ) (E e ζ) (F e ζ))

/-- **The mean of a sampled source matrix is the exact rank-one source operator**, when the
frames represent the source vectors. Source: Theorem 5.2, `eq:compression-random-source`,
`04-compression.tex`, lines 279–309. -/
theorem integral_sampledSourceMatrix (hk : 0 < k) (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (e : w.sourceLocations) (ξ ζ : w.branchLabels e.1) :
    (∫ ω, sampledSourceMatrix w k lam E F e ξ ζ ω ∂sourceGaussianLaw w k) =
      exactSourceMatrix w e ξ ζ := by
  have hmp := measurePreserving_sourceGaussian_eval w k e ξ ζ
  have hi := integrable_ambientSampledSource k hk (lam e ξ) (lam e ζ) (hnonneg e ξ)
    (hnonneg e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ)
  have hm := hi.aestronglyMeasurable
  rw [← hmp.map_eq] at hm
  have heq := (integral_map hmp.measurable.aemeasurable hm).symm
  rw [hmp.map_eq, integral_ambientSampledSource k hk _ _ (hnonneg e ξ) (hnonneg e ζ),
    schmidtFrameOuterProduct, hsource, hsource] at heq
  exact heq

/-- **The corrections have mean zero.** Source: Theorem 5.2, `04-compression.tex`,
lines 279–340. -/
theorem integral_sourceGaussianCorrection (hk : 0 < k) (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (e : w.sourceLocations) (ξ ζ : w.branchLabels e.1) :
    (∫ ω, sourceGaussianCorrection w k lam E F ω e ξ ζ ∂sourceGaussianLaw w k) = 0 := by
  change (∫ ω, sampledSourceMatrix w k lam E F e ξ ζ ω - exactSourceMatrix w e ξ ζ
    ∂sourceGaussianLaw w k) = 0
  rw [integral_sub (integrable_sampledSourceMatrix w k lam E F hk hnonneg e ξ ζ)
    (integrable_const _), integral_sampledSourceMatrix w k lam E F hk hnonneg hsource]
  simp

end Frames

/-- **Schmidt frames whose sampled source matrices are integrable and unbiased**: the frames are
chosen from the source vectors alone, before any corrected set or partial branch. Source:
Theorem 5.2, `04-compression.tex`, lines 279–340. -/
theorem exists_unbiased_sampledSourceMatrix (w : SourceCircuit X Y) (k : ℕ) (hk : 0 < k) :
    ∃ (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
        Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
      (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
        Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
      (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
        Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ),
      (∀ e ξ, (∀ j, 0 ≤ lam e ξ j) ∧ ∑ j, lam e ξ j = 1 ∧
        (E e ξ)ᴴ * E e ξ = 1 ∧ (F e ξ)ᴴ * F e ξ = 1 ∧
        schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp) ∧
      ∀ e ξ ζ,
        Integrable (sampledSourceMatrix w k lam E F e ξ ζ) (sourceGaussianLaw w k) ∧
        (∫ ω, sampledSourceMatrix w k lam E F e ξ ζ ω ∂sourceGaussianLaw w k) =
          exactSourceMatrix w e ξ ζ := by
  obtain ⟨lam, E, F, h, _⟩ := exists_local_schmidt_source_frames w
  exact ⟨lam, E, F, h, fun e ξ ζ ↦
    ⟨integrable_sampledSourceMatrix w k lam E F hk (fun e ξ ↦ (h e ξ).1) e ξ ζ,
      integral_sampledSourceMatrix w k lam E F hk (fun e ξ ↦ (h e ξ).1)
        (fun e ξ ↦ (h e ξ).2.2.2.2) e ξ ζ⟩⟩

/-! ### Covariances of the products of correction entries -/

section Coefficients

variable (w : SourceCircuit X Y) (k : ℕ) (hk : 0 < k) (S : Finset w.sourceLocations)
  (ξ ζ : ∀ e : S, w.branchLabels e.1.1)
  (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
  (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
  (i i' l l' : ∀ e : S,
    Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2) ×
      Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2))

include hk hnonneg in
/-- Products of correction entries over the positions of `S` are the selected Gaussian
coefficients of the same positions and fixed labels. Source: Theorem 5.2,
`04-compression.tex`, lines 338–407. -/
theorem sourceCorrection_product_eq_selected (ω : SourceGaussianSamples w k) :
    (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e)) (ω e.1 (ξ e, ζ e)) (i e) (l e)) =
      selectedBranchDensityCoefficient
        (A := fun (e : w.sourceLocations) (_ : w.branchLabels e.1 × w.branchLabels e.1) ↦
          Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
        (C := fun (e : w.sourceLocations) (_ : w.branchLabels e.1 × w.branchLabels e.1) ↦
          Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
        k S (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i l ω :=
  Finset.prod_congr rfl fun e _ ↦
    sourceCorrection_apply k hk _ _ (hnonneg e.1 (ξ e)) (hnonneg e.1 (ζ e)) _ _ _

include hk hnonneg in
/-- The product of two products of correction entries, one conjugated, is integrable. Source:
Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex`, lines 390–407. -/
theorem integrable_sourceCorrection_product_mul_conj :
    Integrable (fun ω : SourceGaussianSamples w k ↦
      (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) *
      conj (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i' e) (l' e))) (sourceGaussianLaw w k) := by
  simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
  exact integrable_selectedBranchDensityCoefficient_mul_conj
    (B := fun e : w.sourceLocations ↦ w.branchLabels e.1 × w.branchLabels e.1)
    (A := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
    (C := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) k S
    (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i i' l l'

include hk hnonneg in
open Classical in
/-- **The covariance of the products of correction entries is diagonal**, with the power
`k ^ (-|S|)` of the number of samples. Source: Theorem 5.2, `eq:compression-product-covariance`,
`04-compression.tex`, lines 390–407. -/
theorem integral_sourceCorrection_product_mul_conj :
    (∫ ω : SourceGaussianSamples w k,
      (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) *
      conj (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i' e) (l' e)) ∂sourceGaussianLaw w k) =
      if i = i' ∧ l = l' then
        (((k : ℝ) ^ (-(S.card : ℝ)) * Real.sqrt
          (pairedProductProbability (fun e : S ↦ lam e.1 (ξ e)) i *
            pairedProductProbability (fun e : S ↦ lam e.1 (ζ e)) l) : ℝ) : ℂ)
      else 0 := by
  simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
  exact integral_selectedBranchDensityCoefficient_mul_conj
    (B := fun e : w.sourceLocations ↦ w.branchLabels e.1 × w.branchLabels e.1)
    (A := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
    (C := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) k hk S
    (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e))
    (fun e ↦ hnonneg e.1 (ξ e)) (fun e ↦ hnonneg e.1 (ζ e)) i i' l l'

include hk hnonneg in
/-- **A nonempty product of correction entries has mean zero.** Source: Theorem 5.2,
`04-compression.tex`, lines 338–407. -/
theorem integral_sourceCorrection_product_eq_zero [Nonempty S] :
    (∫ ω : SourceGaussianSamples w k,
      (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) ∂sourceGaussianLaw w k) = 0 := by
  simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
  exact integral_selectedBranchDensityCoefficient_eq_zero
    (B := fun e : w.sourceLocations ↦ w.branchLabels e.1 × w.branchLabels e.1)
    (A := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
    (C := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) k S
    (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i l

end Coefficients

open Classical in
/-- **Every matrix combination of products of correction entries has integrable trace norm**
for the law of the sources. Source: Theorem 5.2, `04-compression.tex`, lines 383–434. -/
theorem integrable_rectangularTraceNorm_sourceCorrectionSum {m n : Type} [Fintype m]
    [Fintype n] (w : SourceCircuit X Y) (k : ℕ) (hk : 0 < k) (S : Finset w.sourceLocations)
    (ξ ζ : ∀ e : S, w.branchLabels e.1.1)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (M : CorrectedSchmidtCoordinates w S × CorrectedSchmidtCoordinates w S → Matrix m n ℂ) :
    Integrable (fun ω ↦ rectangularTraceNorm
      (∑ q, (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) • M q)) (sourceGaussianLaw w k) := by
  apply ProbabilityTheory.integrable_rectangularTraceNorm_sum
  intro q r
  exact integrable_sourceCorrection_product_mul_conj w k hk S ξ ζ lam hnonneg q.1 r.1 q.2 r.2

end SourceCircuit

end QuantumCircuit.Party
