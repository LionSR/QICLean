/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.TypicalPureState

/-!
# Typical spectral truncation on a physical region

The projection is determined by the original reduced state of one fixed region.
Its normalized action defines a single global vector. Every disjoint region has
selected marginal bounded by its original marginal divided by the selected mass.
For a unit input vector, the same bound holds for regional entropy.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, `07-comparators.tex`, lines 240–247 and `comparator:post-marginal`,
at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:typical-set, comparator:post-marginal.
Provenance-ID: 8753-qic-regional-typical-state-01
Downstream declaration:
FiniteProduct.typicalPureState
Provenance-ID: 8753-qic-regional-typical-state-02
Downstream declaration:
FiniteProduct.split_typicalPureState
Provenance-ID: 8753-qic-regional-typical-state-03
Downstream declaration:
FiniteProduct.norm_typicalPureState
Provenance-ID: 8753-qic-regional-typical-state-04
Downstream declaration:
FiniteProduct.reducedPure_typicalPureState
Provenance-ID: 8753-qic-regional-typical-state-05
Downstream declaration:
FiniteProduct.entropy_typicalPureState_le
Provenance-ID: 8753-qic-regional-typical-state-06
Downstream declaration:
FiniteProduct.reducedPure_typicalPureState_le
-/

open scoped BigOperators Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Matrix

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

private theorem partialTraceRight_reindex_right (e : B ≃ C)
    (ψ : EuclideanSpace ℂ (A × B)) :
    partialTraceRight (vecMulVec
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.refl A).prodCongr e) ψ)
      (star (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.refl A).prodCongr e) ψ))) =
    partialTraceRight (vecMulVec ψ (star ψ)) := by
  ext a a'
  change (∑ c : C, ψ (a, e.symm c) * star (ψ (a', e.symm c))) =
    ∑ b : B, ψ (a, b) * star (ψ (a', b))
  exact e.symm.sum_comp (fun b ↦ ψ (a, b) * star (ψ (a', b)))

private theorem leftFilteredVector_reindex_right (e : B ≃ C) (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    leftFilteredVector P
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.refl A).prodCongr e) ψ) =
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.refl A).prodCongr e)
      (leftFilteredVector P ψ) := by
  rfl

private theorem spectralData_eq_of_eq [DecidableEq A] {ρ σ : Matrix A A ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (h : ρ = σ) (E : Finset A) :
    hρ.spectralRestrictionMass E = hσ.spectralRestrictionMass E ∧
      hρ.spectralSelection E = hσ.spectralSelection E ∧
      hρ.normalizedSpectralRestriction E = hσ.normalizedSpectralRestriction E := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

private theorem typicalPureState_reindex_right [DecidableEq A] (e : B ≃ C)
    (ψ : EuclideanSpace ℂ (A × B)) (E : Finset A) :
    typicalPureState
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.refl A).prodCongr e) ψ) E =
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.refl A).prodCongr e)
      (typicalPureState ψ E) := by
  have hs := spectralData_eq_of_eq
    (posSemidef_vecMulVec_self_star
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        ((Equiv.refl A).prodCongr e) ψ)).partialTraceRight.isHermitian
    (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian
    (partialTraceRight_reindex_right e ψ) E
  simp only [typicalPureState, hs.1, hs.2.1, leftFilteredVector_reindex_right, map_smul]

end Matrix

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (ψ : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (Configuration β X))

local notation "φX" => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) ψ
local notation "hρX" => reducedPure_posSemidef β ψ X
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρX) E

/-- The typical spectral truncation on one physical region, transported back to
global configuration coordinates. It depends only on the projected region and
selected eigenvalue indices, not on any observed region.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
noncomputable def typicalPureState : EuclideanSpace ℂ ((v : V) → β v) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X)).symm
    (Matrix.typicalPureState φX E)

omit [∀ v, DecidableEq (β v)] in
private theorem partialTraceRight_split_state :
    Matrix.partialTraceRight (Matrix.vecMulVec φX (star φX)) = reducedPure β ψ X := rfl

/-- In the canonical region/complement coordinates, the global selected vector
is the spectral truncation of the original state on that region.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem split_typicalPureState :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) (typicalPureState β ψ X E) =
      Matrix.typicalPureState φX E := by
  simp only [typicalPureState, LinearIsometryEquiv.apply_symm_apply]

/-- A positive-mass typical truncation on a physical region is a unit global
vector. No normalization of the original vector is needed for this identity.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_typicalPureState (hz : 0 < zE) : ‖typicalPureState β ψ X E‖ = 1 := by
  have hmdata := Matrix.spectralData_eq_of_eq
    (Matrix.posSemidef_vecMulVec_self_star φX).partialTraceRight.isHermitian
    (hρX).isHermitian (partialTraceRight_split_state β ψ X) E
  simpa only [typicalPureState, LinearIsometryEquiv.norm_map] using
    Matrix.norm_typicalPureState φX E (by simpa only [hmdata.1] using hz)

/-- The actual marginal on the projected physical region is the normalized
spectral restriction of its original reduced matrix.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem reducedPure_typicalPureState (hz : 0 < zE) :
    reducedPure β (typicalPureState β ψ X E) X =
      (hρX).isHermitian.normalizedSpectralRestriction E := by
  have hmdata := Matrix.spectralData_eq_of_eq
    (Matrix.posSemidef_vecMulVec_self_star φX).partialTraceRight.isHermitian
    (hρX).isHermitian (partialTraceRight_split_state β ψ X) E
  rw [← partialTraceRight_split_state β (typicalPureState β ψ X E) X,
    split_typicalPureState]
  exact (Matrix.partialTraceRight_typicalPureState φX E
    (by simpa only [hmdata.1] using hz)).trans hmdata.2.2

variable (B : Finset V) (h : Disjoint X B)

local notation "φABC" => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
  (Equiv.prodCongr (Equiv.refl (Configuration β X)) (complementUnionEquiv β X B h)) φX

omit [∀ v, DecidableEq (β v)] in
private theorem reducedPure_eq_three_marginal :
    Matrix.partialTraceRight (Matrix.partialTraceLeft (Matrix.vecMulVec φABC (star φABC))) =
      reducedPure β ψ B := by
  unfold reducedPure
  rw [← partialTraceLeft_reducedMatrix_union β (Matrix.vecMulVec ψ (star ψ)) X B h]
  ext b b'
  simp only [Matrix.partialTraceRight_apply, Matrix.partialTraceLeft_apply,
    Matrix.submatrix_apply, reducedMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  change (∑ c, ∑ a,
    ψ ((splitEquiv β X).symm (a, (complementUnionEquiv β X B h).symm (b, c))) *
      star (ψ ((splitEquiv β X).symm (a, (complementUnionEquiv β X B h).symm (b', c))))) = _
  simp_rw [split_union_symm]
  exact Finset.sum_comm

private theorem selectedMass_three_marginal :
    Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.posSemidef_vecMulVec_self_star φABC).partialTraceRight.isHermitian E = zE := by
  exact (Matrix.spectralData_eq_of_eq
    (Matrix.posSemidef_vecMulVec_self_star φABC).partialTraceRight.isHermitian
    (hρX).isHermitian
    ((Matrix.partialTraceRight_reindex_right (complementUnionEquiv β X B h) φX).trans
      (partialTraceRight_split_state β ψ X)) E).1

private theorem selected_three_marginal :
    Matrix.partialTraceRight (Matrix.partialTraceLeft
      (Matrix.vecMulVec (Matrix.typicalPureState φABC E) (star (Matrix.typicalPureState φABC E)))) =
      reducedPure β (typicalPureState β ψ X E) B := by
  rw [Matrix.typicalPureState_reindex_right,
    ← split_typicalPureState β ψ X E]
  exact reducedPure_eq_three_marginal β (typicalPureState β ψ X E) X B h

include h in
/-- The actual selected marginal on every disjoint physical region is bounded
by its original marginal divided by the selected mass, in positive-semidefinite
order. The selected global vector depends only on the projected region.

Source: OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem reducedPure_typicalPureState_le (hz : 0 < zE) :
    (zE⁻¹ • reducedPure β ψ B - reducedPure β (typicalPureState β ψ X E) B).PosSemidef := by
  have hmass := selectedMass_three_marginal β ψ X E B h
  have hc := Matrix.partialTraceRight_partialTraceLeft_typicalPureState_le φABC E
    (by simpa only [hmass] using hz)
  simpa only [hmass, reducedPure_eq_three_marginal β ψ X B h,
    selected_three_marginal β ψ X E B h] using hc

include h in
/-- The entropy on every disjoint physical region after typical spectral
truncation is at most its original entropy divided by the selected mass.
The selected global vector is fixed before the observed region is chosen.

Source: OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem entropy_typicalPureState_le (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    entropy β (typicalPureState β ψ X E) B ≤ entropy β ψ B / zE := by
  have hmass := selectedMass_three_marginal β ψ X E B h
  have hc := Matrix.entropy_partialTraceRight_partialTraceLeft_typicalPureState_le φABC E
    (by simpa only [LinearIsometryEquiv.norm_map] using hψ)
    (by simpa only [hmass] using hz)
  rw [vonNeumannEntropy_congr (selected_three_marginal β ψ X E B h) _
      (reducedPure_posSemidef β _ B).isHermitian,
    vonNeumannEntropy_congr (reducedPure_eq_three_marginal β ψ X B h) _
      (reducedPure_posSemidef β ψ B).isHermitian, hmass] at hc
  exact hc

end FiniteProduct
