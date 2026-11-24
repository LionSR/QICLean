/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.Samples
import QICLean.Circuit.Party.Compression.SourceReplacement.CorrectedContraction

/-!
# Corrected terms of sampled sources in Schmidt coordinates

Fix an affected set `A` and a set `S` of source positions with an affected endpoint each. The
Schmidt indices at both endpoints of every selected slot of the partial expansion at `A` form
the partial Schmidt coordinates (`SourceCircuit.PartialSchmidtCoordinates`); placing the columns
of the Schmidt frames at the selected slots and the original vectors elsewhere gives the
partial Schmidt source vectors (`SourceCircuit.partialSchmidtSourceVectors`) and, after the
residual of a branch, the partial Schmidt matrix and output vector
(`SourceCircuit.partialSchmidtMatrix`, `SourceCircuit.partialSchmidtOutput`).

For every sample point and every input matrix, the corrected term of `S` built from the sampled
corrections is the sum over pairs of branches and pairs of Schmidt coordinates of the products of
the entries of the Gaussian corrections times the mixed densities of the partial Schmidt matrices
(`correctedSourceTerm_gaussian_eq_sum`); on a mixed pure input these densities are outer
products of partial Schmidt outputs (`correctedSourceTerm_gaussian_euclideanOuterProduct_eq_sum`).
The branch densities (`SourceCircuit.gaussianSchmidtBranchDensity`) may be indexed by the
positions of `S` instead of the selected slots (`gaussianSchmidtBranchDensity_eq_sum_original`).

Nothing here involves a measure.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.PartialSchmidtCoordinates`,
  `QuantumCircuit.Party.SourceCircuit.partialSchmidtCoordinateEquiv`.
* `QuantumCircuit.Party.SourceCircuit.partialSchmidtSourceVectors`,
  `QuantumCircuit.Party.SourceCircuit.partialSchmidtMatrix`,
  `QuantumCircuit.Party.SourceCircuit.partialSchmidtOutput`.
* `QuantumCircuit.Party.SourceCircuit.gaussianSchmidtBranchDensity`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm_gaussian_eq_sum`,
  `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm_gaussian_euclideanOuterProduct_eq_sum`.
* `QuantumCircuit.Party.SourceCircuit.gaussianSchmidtBranchDensity_eq_sum_original`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 338–434 (equation `eq:compression-product-covariance`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceGaussianContraction.lean`,
`SourceGaussianVectorDensity.lean`, `SourceGaussianBranchReindex.lean` and the definition in
`SourceGaussianBranchDensity.lean` (Apache-2.0). Changes: the slots and the parties are read
along `ManyBody.blockConfigEquiv` instead of owner isometries and orthonormal bases; vectors are
configuration vectors and the mixed pure input is `euclideanOuterProduct ψ φ`.
-/

open Matrix ManyBody ProductSource
open scoped ComplexConjugate

namespace QuantumCircuit.Party

namespace SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

/-- The Schmidt indices at both endpoints of every selected slot of the partial expansion at
`A`; each slot keeps its source position. Source: Theorem 5.2, `04-compression.tex`,
lines 383–434. -/
abbrev PartialSchmidtCoordinates (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) :=
  ∀ i : selectedPartialSlots A w S,
    Fin (min (w.sourceDims (partialSlotEquiv A w i.1).1).1
      (w.sourceDims (partialSlotEquiv A w i.1).1).2) ×
    Fin (min (w.sourceDims (partialSlotEquiv A w i.1).1).1
      (w.sourceDims (partialSlotEquiv A w i.1).1).2)

/-- The partial Schmidt coordinates read at the selected positions, when every selected position
has an affected endpoint. Source: Theorem 5.2, `04-compression.tex`, lines 383–434. -/
noncomputable def partialSchmidtCoordinateEquiv (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    PartialSchmidtCoordinates A w S ≃ CorrectedSchmidtCoordinates w S :=
  Equiv.piCongrLeft
    (fun e : S ↦ Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2) ×
      Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2))
    (selectedPartialSlotEquiv A w S hS)

/-- The reindexed coordinates at the position of a selected slot are those of the slot. -/
theorem partialSchmidtCoordinateEquiv_apply (A : P → Bool) (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (u : PartialSchmidtCoordinates A w S) (i : selectedPartialSlots A w S) :
    partialSchmidtCoordinateEquiv A w S hS u (selectedPartialSlotEquiv A w S hS i) = u i :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

section Frames

variable (A : P → Bool) (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

open Classical in
/-- The Schmidt frame columns at the selected slots, at the labels of the branch `ξ` and the
coordinates `u`, and the original slot vectors elsewhere. Source: Theorem 5.2,
`04-compression.tex`, lines 383–434. -/
noncomputable def partialSchmidtSourceVectors (ξ : Choices A w)
    (u : PartialSchmidtCoordinates A w S) (i : Fin (partialSlots A w).length) :
    EuclideanSpace ℂ ((partialSlotBases A w).left i × (partialSlotBases A w).right i) :=
  if h : i ∈ selectedPartialSlots A w S then
    EuclideanSpace.vecKron
      (WithLp.toLp 2 fun x ↦ E (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) x
        (u ⟨i, h⟩).1)
      (WithLp.toLp 2 fun x ↦ F (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) x
        (u ⟨i, h⟩).2)
  else partialSlotVector A w ξ i

variable [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- The residual of the branch `ξ` after preparing the partial Schmidt source vectors, read back
on the parties. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
noncomputable def partialSchmidtMatrix (ξ : Choices A w) (u : PartialSchmidtCoordinates A w S) :
    Matrix (Config Y) (Config X) ℂ :=
  reindex (blockConfigEquiv (affectedOwner A) Y) (blockConfigEquiv (affectedOwner A) X)
    ((partialResidual A w ξ).preparedMatrix (partialSlots A w) (partialSlotBases A w)
      (partialSchmidtSourceVectors A w S E F ξ u) (blockSystem (affectedOwner A) X))

/-- The output vector of the partial Schmidt matrix on an input vector. Source: Theorem 5.2,
`04-compression.tex`, lines 409–434. -/
noncomputable def partialSchmidtOutput (ξ : Choices A w) (u : PartialSchmidtCoordinates A w S)
    (ψ : EuclideanSpace ℂ (Config X)) : EuclideanSpace ℂ (Config Y) :=
  Matrix.toEuclideanLin (partialSchmidtMatrix A w S E F ξ u) ψ

/-- **The corrected term of the sampled corrections in Schmidt coordinates**: for every sample
and every input matrix, a sum over pairs of branches and pairs of partial Schmidt coordinates of
the products of entries of the Gaussian corrections at the selected slots times the mixed
densities of the partial Schmidt matrices; every gate coefficient occurs once. Source:
Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex`, lines 338–434. -/
theorem correctedSourceTerm_gaussian_eq_sum
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (ω : SourceGaussianSamples w k) (ρ : Matrix (Config X) (Config X) ℂ) :
    correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        ∑ u : PartialSchmidtCoordinates A w S, ∑ v : PartialSchmidtCoordinates A w S,
          (∏ i : selectedPartialSlots A w S,
            sourceCorrection k (lam _ (partialSlotChoice A w ξ i.1))
              (lam _ (partialSlotChoice A w ζ i.1))
              (ω _ (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) •
            (partialSchmidtMatrix A w S E F ξ u * ρ * (partialSchmidtMatrix A w S E F ζ v)ᴴ) := by
  classical
  rw [correctedSourceTerm_eq_sourceContraction A w S hS]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ congrArg (_ • ·) ?_
  simp_rw [sourceGaussianCorrection_eq_kroneckerSandwich w k lam E F hsource]
  have h := Word.sourceContraction_preparedDensityCoefficient_selected_frames (partialSlots A w)
    (partialSlotBases A w) (blockSystem (affectedOwner A) X)
    (fun i j ↦ WithLp.toLp 2 fun x ↦ E (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) x j)
    (fun i j ↦ WithLp.toLp 2 fun x ↦ F (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) x j)
    (fun i j ↦ WithLp.toLp 2 fun x ↦ E (partialSlotEquiv A w i).1 (partialSlotChoice A w ζ i) x j)
    (fun i j ↦ WithLp.toLp 2 fun x ↦ F (partialSlotEquiv A w i).1 (partialSlotChoice A w ζ i) x j)
    (partialSlotVector A w ξ) (partialSlotVector A w ζ) (selectedPartialSlots A w S)
    (fun i ↦ sourceCorrection k (lam _ (partialSlotChoice A w ξ i))
      (lam _ (partialSlotChoice A w ζ i))
      (ω _ (partialSlotChoice A w ξ i, partialSlotChoice A w ζ i)))
    (partialResidual A w ξ) (partialResidual A w ζ)
    (reindex (blockConfigEquiv (affectedOwner A) X).symm
      (blockConfigEquiv (affectedOwner A) X).symm ρ)
  refine (congrArg (reindex (blockConfigEquiv (affectedOwner A) Y)
    (blockConfigEquiv (affectedOwner A) Y)) h).trans ?_
  rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [LinearEquiv.map_smul, Matrix.coe_reindexLinearEquiv, ← reindex_mul_mul_conjTranspose]
  rfl

/-- **On a mixed pure input, the corrected term of the sampled corrections is a sum of mixed
outer products of partial Schmidt outputs**, with the same Gaussian weights. Source:
Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex`, lines 383–434. -/
theorem correctedSourceTerm_gaussian_euclideanOuterProduct_eq_sum
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (hsource : ∀ e ξ, schmidtFrameVector (lam e ξ) (E e ξ) (F e ξ) = (w.sourceVectorAt e ξ).ofLp)
    (ω : SourceGaussianSamples w k) (ψ φ : EuclideanSpace ℂ (Config X)) :
    correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω)
        (euclideanOuterProduct ψ φ) =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        ∑ u : PartialSchmidtCoordinates A w S, ∑ v : PartialSchmidtCoordinates A w S,
          (∏ i : selectedPartialSlots A w S,
            sourceCorrection k (lam _ (partialSlotChoice A w ξ i.1))
              (lam _ (partialSlotChoice A w ζ i.1))
              (ω _ (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) •
            euclideanOuterProduct (partialSchmidtOutput A w S E F ξ u ψ)
              (partialSchmidtOutput A w S E F ζ v φ) := by
  rw [correctedSourceTerm_gaussian_eq_sum A w S E F hS k lam hsource]
  simp only [partialSchmidtOutput, euclideanOuterProduct, mul_vecMulVec, vecMulVec_mul,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp, star_mulVec]

end Frames

variable [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)] (A : P → Bool) (w : SourceCircuit X Y) (S : Finset w.sourceLocations)

/-- The sampled Gaussian density of one pair of branches, before the two gate coefficients.
Source: Theorem 5.2, `04-compression.tex`, lines 383–434. -/
noncomputable def gaussianSchmidtBranchDensity (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) (ψ φ : EuclideanSpace ℂ (Config X)) (ξ ζ : Choices A w) :
    Matrix (Config Y) (Config Y) ℂ :=
  ∑ u : PartialSchmidtCoordinates A w S, ∑ v : PartialSchmidtCoordinates A w S,
    (∏ i : selectedPartialSlots A w S,
      sourceCorrection k (lam _ (partialSlotChoice A w ξ i.1))
        (lam _ (partialSlotChoice A w ζ i.1))
        (ω _ (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) •
      euclideanOuterProduct (partialSchmidtOutput A w S E F ξ u ψ)
        (partialSchmidtOutput A w S E F ζ v φ)

open Classical in
/-- **The branch density indexed by the selected positions** instead of the selected slots, with
the labels of the branches at the touched gates. Source: Theorem 5.2, `04-compression.tex`,
lines 383–434. -/
theorem gaussianSchmidtBranchDensity_eq_sum_original
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) (ψ φ : EuclideanSpace ℂ (Config X)) (ξ ζ : Choices A w) :
    gaussianSchmidtBranchDensity A w S k lam E F ω ψ φ ξ ζ =
      ∑ u : CorrectedSchmidtCoordinates w S, ∑ v : CorrectedSchmidtCoordinates w S,
        (∏ s : S, sourceCorrection k
          (lam s.1 (choiceAt A w ξ s.1.1 (isTouched_of_source_endpoint A w s.1 (hS s.1 s.2))))
          (lam s.1 (choiceAt A w ζ s.1.1 (isTouched_of_source_endpoint A w s.1 (hS s.1 s.2))))
          (ω s.1 (choiceAt A w ξ s.1.1 (isTouched_of_source_endpoint A w s.1 (hS s.1 s.2)),
            choiceAt A w ζ s.1.1 (isTouched_of_source_endpoint A w s.1 (hS s.1 s.2))))
          (u s) (v s)) •
          euclideanOuterProduct
            (partialSchmidtOutput A w S E F ξ ((partialSchmidtCoordinateEquiv A w S hS).symm u) ψ)
            (partialSchmidtOutput A w S E F ζ ((partialSchmidtCoordinateEquiv A w S hS).symm v)
              φ) := by
  unfold gaussianSchmidtBranchDensity
  refine Fintype.sum_equiv (partialSchmidtCoordinateEquiv A w S hS) _ _ fun u ↦ ?_
  refine Fintype.sum_equiv (partialSchmidtCoordinateEquiv A w S hS) _ _ fun v ↦ ?_
  simp only [Equiv.symm_apply_apply]
  congr 1
  refine Fintype.prod_equiv (selectedPartialSlotEquiv A w S hS) _ _ fun i ↦ ?_
  rw [partialSchmidtCoordinateEquiv_apply, partialSchmidtCoordinateEquiv_apply]
  rfl

end SourceCircuit

end QuantumCircuit.Party
