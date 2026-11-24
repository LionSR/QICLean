/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.Density
import QICLean.Analysis.TensorProduct.ProductSource
import QICLean.Channel.Schmidt.SchmidtFrames

/-!
# Gaussian sample points of the sources of a source circuit

Every source position of a source circuit and every ordered pair of labels of its gate receive
their own point `ω e (ξ, ζ)` of a real Euclidean space: `k` arrays of complex coordinates indexed
by pairs of Schmidt indices (`SourceCircuit.SourceGaussianSamples`). From Schmidt weights `lam`
and Schmidt frames `E`, `F` of the source vectors, a point determines the two endpoint matrices
(`SourceCircuit.sampledEndpointLeft`, `SourceCircuit.sampledEndpointRight`) and their Kronecker
average, the sampled source matrix (`SourceCircuit.sampledSourceMatrix`). The sampled matrix
minus the exact rank-one source operator is the correction
(`SourceCircuit.sourceGaussianCorrection`), which is the correction of the Schmidt vectors
carried by the frames (`sourceGaussianCorrection_eq_kroneckerSandwich`). For every point, the
physical error of the sampled operators is the sum of the physical corrected terms of the
nonempty sets of positions (`physical_sampledSourceMatrix_sub_eq_sum`).

Nothing here involves a measure: the law of the points is in
`QICLean.Circuit.Party.Compression.SourceSampling.Law`.

The rows of the frames at a position `e` are the two slot bases `w.leftBasis e`, `w.rightBasis e`;
the Schmidt index is `Fin (min (w.sourceDims e).1 (w.sourceDims e).2)`, where `w.sourceDims e` is
the pair of cardinalities of these two bases, as in `Matrix.exists_schmidtFrames`.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.SourceGaussianSamples`.
* `QuantumCircuit.Party.SourceCircuit.sampledEndpointLeft`,
  `QuantumCircuit.Party.SourceCircuit.sampledEndpointRight`,
  `QuantumCircuit.Party.SourceCircuit.sampledSourceMatrix`.
* `QuantumCircuit.Party.SourceCircuit.sourceGaussianCorrection`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.exists_local_schmidt_source_frames`.
* `QuantumCircuit.Party.SourceCircuit.sampledSourceMatrix_eq_endpoint_average`.
* `QuantumCircuit.Party.SourceCircuit.sourceGaussianCorrection_eq_kroneckerSandwich`.
* `QuantumCircuit.Party.SourceCircuit.physical_sampledSourceMatrix_sub_eq_sum`,
  `QuantumCircuit.Party.SourceCircuit.rectangularTraceNorm_physical_sampledSourceMatrix_sub_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 279–383 (equations `eq:compression-random-source`, `eq:compression-subset-expansion`,
  `eq:compression-total-error`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceGaussianLaw.lean` (sample type and
sampled matrices), `SampledEndpointFactors.lean`, `SourceCircuitSchmidtSources.lean` and the
deterministic part of `SourceGaussianDensity.lean` (Apache-2.0). Changes: the rows of the
Schmidt frames are the slot bases instead of `Fin` of their cardinalities, so the source vectors
are their own coordinates (the old `sourceCoordinates` is gone); the physical output is read
through a readout matrix `K`.
-/

open Matrix ManyBody ProductSource
open scoped ComplexConjugate Kronecker

namespace QuantumCircuit.Party

namespace SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

/-- The sample space of the sources: at every source position and ordered pair of labels of its
gate, `k` arrays of complex coordinates (as pairs of real coordinates) indexed by pairs of
Schmidt indices. Source: Theorem 5.2, `04-compression.tex`, lines 279–340. -/
abbrev SourceGaussianSamples (w : SourceCircuit X Y) (k : ℕ) :=
  ∀ e : w.sourceLocations, (w.branchLabels e.1 × w.branchLabels e.1) →
    EuclideanSpace ℝ ((Fin k × (Fin (min (w.sourceDims e).1 (w.sourceDims e).2) ×
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2))) × Fin 2)

/-- **Schmidt weights and frames of the source vectors**, chosen for every position and every
label of its gate before any affected set or partial expansion: probability weights `lam`,
isometric frames `E`, `F` representing the source vector. The rows are indexed by
the bases of the two slot registers and the columns by the common Schmidt index.
Thus the orthonormal vectors in the two registers in the proof of Theorem 5.2 are exactly
the columns, and orthonormality is expressed by `Eᴴ * E = 1` and `Fᴴ * F = 1`.
The same choice represents every partial slot vector and its mixed outer products.
Source: Theorem 5.2, `04-compression.tex`, lines 279–309 and 342–417. -/
theorem exists_local_schmidt_source_frames (w : SourceCircuit X Y) :
    ∃ lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
        Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ,
      ∃ E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
          Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ,
        ∃ F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
            Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ,
          (∀ e ξ, (∀ j, 0 ≤ lam e ξ j) ∧ ∑ j, lam e ξ j = 1 ∧
            (E e ξ)ᴴ * E e ξ = 1 ∧ (F e ξ)ᴴ * F e ξ = 1 ∧
            schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp) ∧
          ∀ (A : P → Bool) (ξ ζ : Choices A w) (i : Fin (partialSlots A w).length),
            schmidtFrameVector (lam _ (partialSlotChoice A w ξ i))
                (E _ (partialSlotChoice A w ξ i)) (F _ (partialSlotChoice A w ξ i)) =
                (partialSlotVector A w ξ i).ofLp ∧
              schmidtFrameOuterProduct (lam _ (partialSlotChoice A w ξ i))
                  (lam _ (partialSlotChoice A w ζ i))
                  (E _ (partialSlotChoice A w ξ i)) (F _ (partialSlotChoice A w ξ i))
                  (E _ (partialSlotChoice A w ζ i)) (F _ (partialSlotChoice A w ζ i)) =
                vecMulVec (partialSlotVector A w ξ i).ofLp
                  (fun p ↦ conj (partialSlotVector A w ζ i p)) := by
  choose lam E F hnonneg hmass hE hF hrepr using fun (e : w.sourceLocations)
    (ξ : w.branchLabels e.1) ↦ exists_schmidtFrames_of_norm_eq_one (w.sourceVectorAt e ξ)
      (w.norm_sourceVectorAt e ξ)
  refine ⟨lam, E, F, fun e ξ ↦ ⟨hnonneg e ξ, hmass e ξ, hE e ξ, hF e ξ, hrepr e ξ⟩,
    fun A ξ ζ i ↦ ⟨hrepr _ _, ?_⟩⟩
  exact congrArg₂ vecMulVec (hrepr _ _)
    (funext fun q ↦ congrArg (starRingEnd ℂ) (congrFun (hrepr _ _) q))

variable [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : SourceCircuit X Y) (k : ℕ)
  (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The left endpoint matrix of the `j`-th sample at a position and an ordered pair of labels.
Source: Theorem 5.2, `eq:compression-random-source`, `04-compression.tex`, lines 279–309. -/
noncomputable def sampledEndpointLeft (e : w.sourceLocations)
    (ξζ : w.branchLabels e.1 × w.branchLabels e.1) (j : Fin k) (ω : SourceGaussianSamples w k) :
    Matrix (w.leftBasis e) (w.leftBasis e) ℂ :=
  ambientSourceU k (lam e ξζ.1) (lam e ξζ.2) (E e ξζ.1) (E e ξζ.2) j (ω e ξζ)

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The right endpoint matrix: the conjugates of the same Gaussian array and the same sample
index as the left endpoint. Source: Theorem 5.2, `04-compression.tex`, lines 279–309. -/
noncomputable def sampledEndpointRight (e : w.sourceLocations)
    (ξζ : w.branchLabels e.1 × w.branchLabels e.1) (j : Fin k) (ω : SourceGaussianSamples w k) :
    Matrix (w.rightBasis e) (w.rightBasis e) ℂ :=
  ambientSourceV k (lam e ξζ.1) (lam e ξζ.2) (F e ξζ.1) (F e ξζ.2) j (ω e ξζ)

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- **The sampled source matrix** at a position and ket and bra labels: the average of the
Kronecker products of the frame-carried Gaussian factors; no rank-one condition is imposed.
Source: Theorem 5.2, `eq:compression-random-source`, `04-compression.tex`, lines 279–309. -/
noncomputable def sampledSourceMatrix (e : w.sourceLocations) (ξ ζ : w.branchLabels e.1)
    (ω : SourceGaussianSamples w k) :
    Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ :=
  ambientSampledSource k (lam e ξ) (lam e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ) (ω e (ξ, ζ))

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- **The sampled source matrix is the average of its two endpoint factors**, also for `k = 0`.
Source: Theorem 5.2, `04-compression.tex`, lines 279–309. -/
theorem sampledSourceMatrix_eq_endpoint_average (e : w.sourceLocations)
    (ξ ζ : w.branchLabels e.1) (ω : SourceGaussianSamples w k) :
    sampledSourceMatrix w k lam E F e ξ ζ ω =
      (k : ℂ)⁻¹ • ∑ j : Fin k,
        sampledEndpointLeft w k lam E e (ξ, ζ) j ω ⊗ₖ
          sampledEndpointRight w k lam F e (ξ, ζ) j ω :=
  rfl

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The correction of the sampled source matrices: the sampled matrix minus the exact rank-one
source operator, at every position and pair of labels. Source: Theorem 5.2,
`eq:compression-random-source`, `04-compression.tex`, lines 279–309. -/
noncomputable def sourceGaussianCorrection (ω : SourceGaussianSamples w k) :
    ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ :=
  (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω) - exactSourceMatrix w

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- **The correction is the correction of the Schmidt vectors carried by the frames**, when the
frames represent the source vectors. Source: Theorem 5.2, `04-compression.tex`,
lines 279–338. -/
theorem sourceGaussianCorrection_eq_kroneckerSandwich
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (ω : SourceGaussianSamples w k) (e : w.sourceLocations) (ξ ζ : w.branchLabels e.1) :
    sourceGaussianCorrection w k lam E F ω e ξ ζ =
      kroneckerSandwich (E e ξ) (F e ξ) (E e ζ) (F e ζ)
        (sourceCorrection k (lam e ξ) (lam e ζ) (ω e (ξ, ζ))) := by
  have hs : exactSourceMatrix w e ξ ζ =
      schmidtFrameOuterProduct (lam e ξ) (lam e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ) := by
    rw [schmidtFrameOuterProduct, hsource, hsource]
    rfl
  change ambientSampledSource k (lam e ξ) (lam e ζ) (E e ξ) (F e ξ) (E e ζ) (F e ζ) (ω e (ξ, ζ)) -
    exactSourceMatrix w e ξ ζ = _
  rw [hs]
  exact ambientSourceCorrection_eq_kroneckerSandwich k (lam e ξ) (lam e ζ) (E e ξ) (F e ξ)
    (E e ζ) (F e ζ) (ω e (ξ, ζ))

variable [Fintype P] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {Phys Env : Type} [Fintype Env]

open Classical in
/-- **For every sample, the physical error of the sampled source operators is the sum of the
nonempty physical corrected terms**, the discarded factor traced. Source: Theorem 5.2,
`eq:compression-subset-expansion`, `04-compression.tex`, lines 338–383. -/
theorem physical_sampledSourceMatrix_sub_eq_sum (K : Matrix (Phys × Env) (Config Y) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) (ω : SourceGaussianSamples w k) :
    physicalSourceReplacedDensity w (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω) K ρ -
        physicalDensity w K ρ =
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        physicalCorrectedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) K ρ := by
  simpa only [sourceGaussianCorrection, sub_add_cancel] using
    physicalSourceReplacedDensity_sub_exact w (sourceGaussianCorrection w k lam E F ω) K ρ

open Classical in
/-- **For every sample, the physical trace-norm error is at most the sum of the trace norms of
the nonempty physical corrected terms**, with no factor depending on the discarded factor.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex`, lines 338–383. -/
theorem rectangularTraceNorm_physical_sampledSourceMatrix_sub_le [Fintype Phys] [DecidableEq Phys]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ)
    (ω : SourceGaussianSamples w k) :
    rectangularTraceNorm
        (physicalSourceReplacedDensity w (fun e ξ ζ ↦ sampledSourceMatrix w k lam E F e ξ ζ ω) K ρ -
          physicalDensity w K ρ) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        rectangularTraceNorm
          (physicalCorrectedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) K ρ) := by
  rw [physical_sampledSourceMatrix_sub_eq_sum]
  exact rectangularTraceNorm_sum_le _ _

end SourceCircuit

end QuantumCircuit.Party
