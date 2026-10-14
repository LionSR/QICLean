/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedSharpTree
import QICLean.Representation.CompressedTypicalLabelMass
import QICLean.Analysis.IsometricDomainExtension

/-!
# The literal auxiliary-sector mass after selected Bell insertion

The original and compressed auxiliary sectors are intertwined by the actual
Bell insertion. Its unit inserted vector makes it an isometry, so the masses
agree exactly for every supplied label and copy number. The second equality
identifies this mass with the one in the existing Schmidt--Bell label-sequence
theorem. It makes no label choice and assumes no lower mass estimate.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 255--290
and 383--404, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators Matrix Kronecker

noncomputable section

namespace TensorPower

section GeneralInsertion

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (C R : Type)
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

/-- The same auxiliary label passes through the actual Bell insertion. -/
theorem labelProj_mul_bellInsertion_auxiliary (k : ℕ)
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (b : Configuration β X × C → ℂ) :
    let J := (addedSiteInsertion (compressedSiteSpace β X R)
      (Configuration β X × C) k b).submatrix
        (bellInsertionCopyEquiv β X C R k) id
    labelProj (subsystemPerm k (addedSiteSpace (addedSiteSpace β C) R) {none}) ell * J =
      J * labelProj (subsystemPerm k (compressedSiteSpace β X R) {none}) ell := by
  classical
  simpa [labelObservable] using
    labelObservable_mul_bellInsertion_auxiliary β X C R k
      (fun l ↦ if l = ell then 1 else 0) b

/-- Actual unit Bell insertion preserves every supplied auxiliary-label norm. -/
theorem norm_labelProj_bellInsertion_auxiliary (k : ℕ)
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (b : Configuration β X × C → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1)
    (ψ : EuclideanSpace ℂ (Config k (compressedSiteSpace β X R))) :
    let J := (addedSiteInsertion (compressedSiteSpace β X R)
      (Configuration β X × C) k b).submatrix
        (bellInsertionCopyEquiv β X C R k) id
    ‖toEuclideanLin
      (labelProj (subsystemPerm k (addedSiteSpace (addedSiteSpace β C) R) {none}) ell)
      (toEuclideanLin J ψ)‖ =
    ‖toEuclideanLin
      (labelProj (subsystemPerm k (compressedSiteSpace β X R) {none}) ell) ψ‖ := by
  intro J
  have hJ : Jᴴ * J = 1 := isIsometry_bellInsertion β X C R k b hb
  have hmove := labelProj_mul_bellInsertion_auxiliary β X C R k ell b
  change ‖WithLp.toLp 2
      (labelProj (subsystemPerm k (addedSiteSpace (addedSiteSpace β C) R) {none}) ell *ᵥ
        (J *ᵥ ψ.ofLp))‖ = _
  rw [Matrix.mulVec_mulVec, hmove, ← Matrix.mulVec_mulVec]
  exact Matrix.norm_toLp_mulVec_of_isometry J hJ _

end GeneralInsertion

-- Match the finite-Pi decision procedures in the literal postvector definition.
attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The literal selected Bell postvector and the literal compressed-site state
have exactly the same squared mass in every supplied auxiliary label. The
physical vector need not be normalized; only its actual selected mass is
positive. Zero copies are included. -/
theorem norm_sq_labelProj_selectedBellPost_eq
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k : ℕ) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let Ψ := WithLp.toLp 2
      (fun x : Config k (compressedSiteSpace β X (Fin E.card)) ↦
        ∏ j, χ (Equiv.piOptionEquivProd (x j)))
    ‖toEuclideanLin
      (labelProj (subsystemPerm k
        (addedSiteSpace (addedSiteSpace β E) (Fin E.card)) {none}) ell)
      (selectedBellPost β Ω X E k)‖ ^ 2 =
    ‖toEuclideanLin
      (labelProj (subsystemPerm k (compressedSiteSpace β X (Fin E.card)) {none}) ell)
      Ψ‖ ^ 2 := by
  intro ΩX χ Ψ
  let b : Configuration β X × E → ℂ := Matrix.selectedBellVector ΩX E
  have hb : ‖WithLp.toLp 2 b‖ = 1 := by
    simpa only [b, WithLp.toLp_ofLp] using Matrix.norm_selectedBellVector ΩX E hz
  have hn := norm_labelProj_bellInsertion_auxiliary β X E (Fin E.card) k ell b hb Ψ
  exact congrArg (fun r : ℝ ↦ r ^ 2) hn

/-- The actual postvector mass is precisely the mass in the already available
Schmidt--Bell prevector theorem, for the very same label. This equality can be
applied pointwise to an existing chosen sequence, retaining all its prevector,
energy, symmetry, both-label and entropy-asymptotic conclusions. -/
theorem norm_sq_labelProj_selectedBellPost_prod
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k : ℕ) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ψ : Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    ‖toEuclideanLin
      (labelProj (subsystemPerm k
        (addedSiteSpace (addedSiteSpace β E) (Fin E.card)) {none}) ell)
      (selectedBellPost β Ω X E k)‖ ^ 2 =
    ‖WithLp.toLp 2
      (((1 : Matrix (Fin k → Configuration β Xᶜ)
        (Fin k → Configuration β Xᶜ) ℂ) ⊗ₖ
          labelProj (copyPerm (Fin E.card) k) ell) *ᵥ
        (fun x : (Fin k → Configuration β Xᶜ) × (Fin k → Fin E.card) ↦
          ∏ j, ψ (x.1 j, x.2 j)))‖ ^ 2 := by
  intro ΩX ψ
  exact (norm_sq_labelProj_selectedBellPost_eq β Ω X E hz k ell).trans
    (norm_sq_labelProj_compressedTypicalSite_prod β X k Ω E ell)

end TensorPower
