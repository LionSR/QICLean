/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.Law
import QICLean.Circuit.Party.Compression.SourceSampling.SchmidtCoordinates
import QICLean.Analysis.Real.SampleCount
import Mathlib.MeasureTheory.Integral.Average

/-!
# Integrable errors of the sampled sources and the choice of one sample

The products of entries of the sampled corrections have finite second moments
(`sourceCorrection_product_memLp_two`, `partialSourceCorrection_product_memLp_two`), so every
fixed linear image of a corrected term of the sampled corrections has integrable trace norm
(`integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian`), in particular every
physical corrected term (`integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian`).
Some sample has physical error at most the sum of the expected trace norms of the nonempty
physical corrected terms (`exists_sampledSourceMatrix_error_le_sum_integral`); the expected norm
of a corrected term is at most the coefficient-weighted sum of the expected norms of its branch
densities (`integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum`). At the
sample count `binomialSampleCount (max 1 N) Q ε`, `N` the number of source positions, bounds
`Q ^ |S| k ^ (-|S|/2)` on the expected corrected terms give one sample with physical error at
most `ε / 4` (`exists_sampledSourceMatrix_error_le_of_integral_bound`).

This module takes integrals, and is one of the modules of
`Circuit/Party/Compression/SourceSampling` allowed to import `QICLean.Probability`.

## Main results

In namespace `QuantumCircuit.Party.SourceCircuit`:

* `integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian`,
  `integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian`.
* `exists_sampledSourceMatrix_error_le_sum_integral`.
* `integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum`.
* `exists_sampledSourceMatrix_error_le_of_integral_bound`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 338–434 and 540–558 (equations `eq:compression-product-covariance`,
  `eq:compression-total-error`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceGaussianMoments.lean`,
`SourceGaussianPhysicalIntegrability.lean`, the expectations of
`SourceGaussianBranchDensity.lean` and `SourceSampleChoice.lean` (Apache-2.0). Changes: the
physical output is read through a readout matrix `K`; the old count `sourceSamplingCount N Q ε`
is `binomialSampleCount (max 1 N) Q ε` (`QICLean.Analysis.Real.SampleCount`).
-/

open MeasureTheory Matrix ManyBody ProductSource QICLean.ComplexGaussian
open scoped ComplexConjugate

namespace QuantumCircuit.Party

namespace SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

/-- Products of correction entries over the positions of `S` have finite second moment, for
fixed labels. Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex`,
lines 390–407. -/
theorem sourceCorrection_product_memLp_two (w : SourceCircuit X Y) (k : ℕ) (hk : 0 < k)
    (S : Finset w.sourceLocations) (ξ ζ : ∀ e : S, w.branchLabels e.1.1)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j) (i l : CorrectedSchmidtCoordinates w S) :
    MemLp (fun ω : SourceGaussianSamples w k ↦
      ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) 2 (sourceGaussianLaw w k) := by
  have hm : Integrable (fun ω : SourceGaussianSamples w k ↦
      ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) (sourceGaussianLaw w k) := by
    simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
    exact integrable_selectedBranchDensityCoefficient
      (B := fun e : w.sourceLocations ↦ w.branchLabels e.1 × w.branchLabels e.1)
      (A := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2))
      (C := fun e _ ↦ Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) k S
      (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i l
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [norm_mul, Complex.norm_conj, ← pow_two] using
    (integrable_sourceCorrection_product_mul_conj w k hk S ξ ζ lam hnonneg i i l l).norm

/-- Products of correction entries over the selected slots of a partial expansion have finite
second moment; the slots keep the labels of the branches. Source: Theorem 5.2,
`eq:compression-product-covariance`, `04-compression.tex`, lines 390–407. -/
theorem partialSourceCorrection_product_memLp_two (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (ξ ζ : Choices A w) (u v : PartialSchmidtCoordinates A w S) :
    MemLp (fun ω : SourceGaussianSamples w k ↦
      ∏ i : selectedPartialSlots A w S,
        sourceCorrection k (lam _ (partialSlotChoice A w ξ i.1))
          (lam _ (partialSlotChoice A w ζ i.1))
          (ω _ (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i))
      2 (sourceGaussianLaw w k) := by
  let ξ₀ := fun e : S ↦ choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
  let ζ₀ := fun e : S ↦ choiceAt A w ζ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
  have he (ω : SourceGaussianSamples w k) :
      (∏ i : selectedPartialSlots A w S,
        sourceCorrection k (lam _ (partialSlotChoice A w ξ i.1))
          (lam _ (partialSlotChoice A w ζ i.1))
          (ω _ (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) =
      ∏ e : S, sourceCorrection k (lam e.1 (ξ₀ e)) (lam e.1 (ζ₀ e)) (ω e.1 (ξ₀ e, ζ₀ e))
        (partialSchmidtCoordinateEquiv A w S hS u e)
        (partialSchmidtCoordinateEquiv A w S hS v e) := by
    refine Fintype.prod_equiv (selectedPartialSlotEquiv A w S hS) _ _ fun i ↦ ?_
    rw [partialSchmidtCoordinateEquiv_apply, partialSchmidtCoordinateEquiv_apply]
    rfl
  simp_rw [he]
  exact sourceCorrection_product_memLp_two w k hk S ξ₀ ζ₀ lam hnonneg _ _

variable [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

open Classical in
/-- **Every fixed linear image of a corrected term of the sampled corrections has integrable
trace norm**, for every input matrix; partial traces and physical readouts are such images.
Source: Theorem 5.2, `04-compression.tex`, lines 383–434. -/
theorem integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian {r s : Type}
    [∀ p, Finite (Y p)] [Fintype r] [Fintype s] (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (ρ : Matrix (Config X) (Config X) ℂ) (L : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix r s ℂ) :
    Integrable (fun ω ↦ rectangularTraceNorm
      (L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) ρ)))
      (sourceGaussianLaw w k) := by
  classical
  let : ∀ p, Fintype (Y p) := fun p ↦ Fintype.ofFinite (Y p)
  let J := (Choices A w × Choices A w) ×
    (PartialSchmidtCoordinates A w S × PartialSchmidtCoordinates A w S)
  let z (q : J) (ω : SourceGaussianSamples w k) :=
    (coefficient A w q.1.1 * conj (coefficient A w q.1.2)) *
      ∏ i : selectedPartialSlots A w S,
        sourceCorrection k (lam _ (partialSlotChoice A w q.1.1 i.1))
          (lam _ (partialSlotChoice A w q.1.2 i.1))
          (ω _ (partialSlotChoice A w q.1.1 i.1, partialSlotChoice A w q.1.2 i.1))
          (q.2.1 i) (q.2.2 i)
  let M (q : J) := L (partialSchmidtMatrix A w S E F q.1.1 q.2.1 * ρ *
    (partialSchmidtMatrix A w S E F q.1.2 q.2.2)ᴴ)
  have hz (q : J) : MemLp (z q) 2 (sourceGaussianLaw w k) :=
    (partialSourceCorrection_product_memLp_two A w S hS k hk lam hnonneg
      q.1.1 q.1.2 q.2.1 q.2.2).const_mul _
  have he (ω : SourceGaussianSamples w k) :
      L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) ρ) =
        ∑ q : J, z q ω • M q := by
    rw [correctedSourceTerm_gaussian_eq_sum A w S E F hS k lam hsource]
    simp only [J, map_sum, map_smul, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, z, M]
  simp_rw [he]
  exact ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two z hz M

variable [∀ p, Fintype (Y p)] {Phys Env : Type} [Fintype Phys] [DecidableEq Phys] [Fintype Env]

/-- The physical readout `M ↦ Tr_Env (K M Kᴴ)` as a linear map. -/
private noncomputable def physicalReadoutLinearMap (K : Matrix (Phys × Env) (Config Y) ℂ) :
    Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix Phys Phys ℂ where
  toFun M := partialTraceRightLM (α := Phys) (β := Env) (K * M * Kᴴ)
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c M := by simp [Matrix.mul_smul, Matrix.smul_mul]

open Classical in
/-- **Every physical corrected term of the sampled corrections has integrable trace norm**, for
every readout and every input matrix. Source: Theorem 5.2, `04-compression.tex`,
lines 338–434. -/
theorem integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian (A : P → Bool)
    (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    Integrable (fun ω ↦ rectangularTraceNorm
      (physicalCorrectedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) K ρ))
      (sourceGaussianLaw w k) :=
  integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian A w S hS k hk lam hnonneg E F
    hsource ρ (physicalReadoutLinearMap K)

open Classical in
/-- **Some sample has physical error at most the sum of the expected trace norms of the nonempty
physical corrected terms**; integrability is proved, not assumed. Source: Theorem 5.2,
`eq:compression-total-error`, `04-compression.tex`, lines 338–383 and 540–558. -/
theorem exists_sampledSourceMatrix_error_le_sum_integral (w : SourceCircuit X Y) (k : ℕ)
    (hk : 0 < k)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    ∃ ω : SourceGaussianSamples w k,
      rectangularTraceNorm
        (physicalSourceReplacedDensity w (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω)
          K ρ - physicalDensity w K ρ) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        ∫ ω, rectangularTraceNorm
          (physicalCorrectedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) K ρ)
          ∂sourceGaussianLaw w k := by
  let T := (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅
  have hf (S : Finset w.sourceLocations) : Integrable (fun ω ↦ rectangularTraceNorm
      (physicalCorrectedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) K ρ))
      (sourceGaussianLaw w k) :=
    integrable_rectangularTraceNorm_physicalCorrectedSourceTerm_gaussian (fun _ ↦ true) w S
      (fun _ _ ↦ Or.inl rfl) k hk lam hnonneg E F hsource K ρ
  obtain ⟨ω, hω⟩ := exists_le_integral (integrable_finsetSum T fun S _ ↦ hf S)
  refine ⟨ω, (rectangularTraceNorm_physical_sampledSourceMatrix_sub_le w k lam E F K ρ ω).trans ?_⟩
  exact hω.trans_eq (integral_finsetSum T fun S _ ↦ hf S)

open Classical in
/-- **Some sample at the count `binomialSampleCount (max 1 N) Q ε` has physical error at most
`ε / 4`**, `N` the number of source positions, when every nonempty set `S` of positions has
expected physical corrected term at most `Q ^ |S| k ^ (-|S| / 2)`; integrability is proved,
not assumed. Source: Theorem 5.2, `eq:compression-total-error` and the choice of `k`,
`04-compression.tex`, lines 540–558. -/
theorem exists_sampledSourceMatrix_error_le_of_integral_bound (w : SourceCircuit X Y)
    (Q ε : ℝ) (hQ : 0 ≤ Q) (hε : 0 < ε) (hεone : ε ≤ 1)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    let k := binomialSampleCount (max 1 (Fintype.card w.sourceLocations)) Q ε
    (∀ S : Finset w.sourceLocations, S ≠ ∅ →
      (∫ ω, rectangularTraceNorm
        (physicalCorrectedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) K ρ)
        ∂sourceGaussianLaw w k) ≤ Q ^ S.card * (k : ℝ) ^ (-(S.card : ℝ) / 2)) →
    ∃ ω : SourceGaussianSamples w k,
      rectangularTraceNorm
        (physicalSourceReplacedDensity w (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω)
          K ρ - physicalDensity w K ρ) ≤ ε / 4 := by
  intro k hbound
  obtain ⟨ω, hω⟩ := exists_sampledSourceMatrix_error_le_sum_integral w k
    (binomialSampleCount_bounds _ Q ε).1 lam hnonneg E F hsource K ρ
  refine ⟨ω, hω.trans ?_⟩
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        Q ^ S.card * (k : ℝ) ^ (-(S.card : ℝ) / 2) :=
      Finset.sum_le_sum fun S hS ↦ hbound S (Finset.mem_erase.mp hS).1
    _ ≤ ε / 4 := by
      simpa only [Finset.powerset_univ, Finset.card_univ] using
        Finset.sum_powerset_erase_empty_binomialSampleCount_le
          (Finset.univ : Finset w.sourceLocations) Q ε hQ hε hεone

variable [∀ p, DecidableEq (Y p)]

open Classical in
/-- Every fixed linear image of the sampled density of a pair of branches has integrable trace
norm. Source: Theorem 5.2, `04-compression.tex`, lines 383–434. -/
theorem integrable_rectangularTraceNorm_map_gaussianSchmidtBranchDensity {r s : Type}
    [Fintype r] [Fintype s] (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j) (ψ φ : EuclideanSpace ℂ (Config X)) (ξ ζ : Choices A w)
    (L : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix r s ℂ) :
    Integrable (fun ω ↦ rectangularTraceNorm
      (L (gaussianSchmidtBranchDensity A w S k lam E F ω ψ φ ξ ζ))) (sourceGaussianLaw w k) := by
  let z := fun (q : PartialSchmidtCoordinates A w S × PartialSchmidtCoordinates A w S)
      (ω : SourceGaussianSamples w k) ↦
    ∏ i : selectedPartialSlots A w S,
      sourceCorrection k (lam _ (partialSlotChoice A w ξ i.1))
        (lam _ (partialSlotChoice A w ζ i.1))
        (ω _ (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (q.1 i) (q.2 i)
  let M := fun q : PartialSchmidtCoordinates A w S × PartialSchmidtCoordinates A w S ↦
    L (euclideanOuterProduct (partialSchmidtOutput A w S E F ξ q.1 ψ)
      (partialSchmidtOutput A w S E F ζ q.2 φ))
  have h := ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two z
    (fun q ↦ partialSourceCorrection_product_memLp_two A w S hS k hk lam hnonneg ξ ζ q.1 q.2) M
  simpa only [gaussianSchmidtBranchDensity, map_sum, map_smul, Fintype.sum_prod_type, z, M]
    using h

open Classical in
/-- **The expected norm of a fixed linear image of a corrected term of the sampled corrections on
a mixed pure input is at most the sum over pairs of branches of the expected norms of their
sampled densities**, weighted by the norms of the gate coefficients. Source: Theorem 5.2,
`04-compression.tex`, lines 383–434. -/
theorem integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum {r s : Type}
    [Fintype r] [Fintype s] (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (ψ φ : EuclideanSpace ℂ (Config X)) (L : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix r s ℂ) :
    (∫ ω, rectangularTraceNorm (L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω)
        (euclideanOuterProduct ψ φ))) ∂sourceGaussianLaw w k) ≤
      ∑ ξ, ∑ ζ, ‖coefficient A w ξ * conj (coefficient A w ζ)‖ *
        ∫ ω, rectangularTraceNorm (L (gaussianSchmidtBranchDensity A w S k lam E F ω ψ φ ξ ζ))
          ∂sourceGaussianLaw w k := by
  let c := fun q : Choices A w × Choices A w ↦ coefficient A w q.1 * conj (coefficient A w q.2)
  let N := fun (q : Choices A w × Choices A w) (ω : SourceGaussianSamples w k) ↦
    L (gaussianSchmidtBranchDensity A w S k lam E F ω ψ φ q.1 q.2)
  have hN (q : Choices A w × Choices A w) :
      Integrable (fun ω ↦ rectangularTraceNorm (N q ω)) (sourceGaussianLaw w k) :=
    integrable_rectangularTraceNorm_map_gaussianSchmidtBranchDensity A w S k hk lam E F hS
      hnonneg ψ φ q.1 q.2 L
  have he (ω : SourceGaussianSamples w k) :
      L (correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω)
        (euclideanOuterProduct ψ φ)) = ∑ q, c q • N q ω := by
    rw [correctedSourceTerm_gaussian_euclideanOuterProduct_eq_sum A w S E F hS k lam hsource]
    simp only [Fintype.sum_prod_type, map_sum, map_smul, c, N, gaussianSchmidtBranchDensity]
  have hsum := integrable_finsetSum Finset.univ (fun q _ ↦ (hN q).const_mul ‖c q‖)
  have hfull := integrable_rectangularTraceNorm_map_correctedSourceTerm_gaussian A w S hS k hk
    lam hnonneg E F hsource (euclideanOuterProduct ψ φ) L
  calc
    _ ≤ ∫ ω, ∑ q, ‖c q‖ * rectangularTraceNorm (N q ω) ∂sourceGaussianLaw w k := by
      refine integral_mono hfull hsum fun ω ↦ ?_
      dsimp only
      rw [he]
      exact rectangularTraceNorm_sum_smul_le _ _ _
    _ = _ := by
      rw [integral_finsetSum _ (fun q _ ↦ (hN q).const_mul ‖c q‖)]
      simp only [integral_const_mul, Fintype.sum_prod_type, c, N]

end SourceCircuit

end QuantumCircuit.Party
