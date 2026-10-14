/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SelectedBellPostMass
import QICLean.Representation.SchmidtBellPrevectorOverlap
import QICLean.Representation.SchmidtBellWitnessRange
import QICLean.Representation.BellPinnedMetricCoordinates

/-!
# The exact pin identity for the literal selected Bell postvector

The actual physical prevector, its supplied right auxiliary label, the fixed
selected-set enumeration and the exact pin coefficient are retained. The
symmetric pin is obtained from the Bell range pin by proving symmetry of the
same labelled postvector, rather than assuming any vector equality.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 283--299
and 383--418, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators Matrix Kronecker

noncomputable section

namespace TensorPower

attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (Configuration β X)) (k : ℕ)

local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => compressedSiteSpace β X (Fin E.card)
local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "L" => Fin k → A × E

/-- The literal inserted postvector is the pullback of the actual selected
Bell tensor and compressed selected tensor in witness coordinates. -/
theorem selectedBellPost_eq_pullback :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let post : EuclideanSpace ℂ (L × Config k ιe) := WithLp.toLp 2
      (fun x ↦ (∏ j, selectedBellVector ΩX E (x.1 j)) *
        ∏ j, compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x.2 j none), fun v ↦ x.2 j (some v)))
    selectedBellPost β Ω X E k =
      WithLp.toLp 2 (post ∘ schmidtBellWitnessEquiv β X E k) := by
  intro ΩX post
  ext x
  change (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E) *ᵥ
      (fun y : Config k ιe ↦ ∏ j, compressedTypicalPureState ΩX E
        ((Finset.equivFin E).symm (y j none), fun v ↦ y j (some v))))
      (bellInsertionCopyEquiv β X E (Fin E.card) k x) = _
  rw [addedSiteInsertion_mulVec]
  rfl

/-- The supplied auxiliary sector of the literal postvector is symmetric.
The proof uses only the tensor-product construction and the derived
auxiliary-label commutation; no selected-mass or norm hypothesis is needed. -/
theorem symProj_labelProj_selectedBellPost
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let Q := labelProj (subsystemPerm k ι₀ {none}) ell
    toEuclideanLin (symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k))
      (toEuclideanLin Q (selectedBellPost β Ω X E k)) =
        toEuclideanLin Q (selectedBellPost β Ω X E k) := by
  intro Q
  let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
  let χ : ((o : Option ↥(Xᶜ)) → ιe o) → ℂ := fun x ↦
    compressedTypicalPureState ΩX E
      ((Finset.equivFin E).symm (x none), fun v ↦ x (some v))
  let Ψ : Config k ιe → ℂ := fun x ↦ ∏ j, χ (x j)
  let J := (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E)).submatrix
    (bellInsertionCopyEquiv β X E (Fin E.card) k) id
  let Pe := symProj (copyPerm ((o : Option ↥(Xᶜ)) → ιe o) k)
  let Qe := labelProj (subsystemPerm k ιe {none}) ell
  have hΨ : Pe *ᵥ Ψ = Ψ := by
    apply symProj_mulVec_of_mem
    intro σ
    rw [permOp_mulVec]
    funext x
    change (∏ j, χ (x (σ j))) = ∏ j, χ (x j)
    exact Fintype.prod_equiv σ _ _ (fun _ ↦ rfl)
  have hQe : Commute Qe Pe := by
    classical
    simpa [labelObservable] using commute_labelObservable_symProj ιe k {none}
      (fun l ↦ if l = ell then 1 else 0)
  have hQJ : Q * J = J * Qe :=
    labelProj_mul_bellInsertion_auxiliary β X E (Fin E.card) k ell
      (selectedBellVector ΩX E)
  have hSJ := symProj_mul_bellInsertion β X E (Fin E.card) k
    (selectedBellVector ΩX E)
  apply WithLp.ofLp_injective 2
  change symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) *ᵥ
      (Q *ᵥ (J *ᵥ Ψ)) = Q *ᵥ (J *ᵥ Ψ)
  have hQP : Q *ᵥ (J *ᵥ Ψ) = J *ᵥ (Qe *ᵥ Ψ) := by
    rw [Matrix.mulVec_mulVec, hQJ, ← Matrix.mulVec_mulVec]
  have hPeQP : Pe *ᵥ (Qe *ᵥ Ψ) = Qe *ᵥ Ψ := by
    rw [Matrix.mulVec_mulVec, ← hQe.eq, ← Matrix.mulVec_mulVec, hΨ]
  calc
    _ = symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) *ᵥ
        (J *ᵥ (Qe *ᵥ Ψ)) := congrArg (fun w ↦
          symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) *ᵥ w) hQP
    _ = (J * Pe) *ᵥ (Qe *ᵥ Ψ) := by rw [Matrix.mulVec_mulVec, hSJ]
    _ = J *ᵥ (Qe *ᵥ Ψ) := by rw [← Matrix.mulVec_mulVec, hPeQP]
    _ = _ := hQP.symm

/-- The actual symmetric Bell pin of the original supplied-label physical
prevector equals the same supplied auxiliary sector of the literal postvector,
with the exact coefficient `(sqrt z / E.card)^k`. -/
theorem bellPin_schmidtBellPrevector_eq_selectedBellPost
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let z := (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let J := (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E)).submatrix
      (bellInsertionCopyEquiv β X E (Fin E.card) k) id
    let Pe := symProj (copyPerm ((o : Option ↥(Xᶜ)) → ιe o) k)
    let P := J * Pe * Jᴴ
    let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
      (schmidtBellSitePrevector β X E k ΩX ell ∘ schmidtBellWitnessEquiv β X E k)
    let Q := labelProj (subsystemPerm k ι₀ {none}) ell
    toEuclideanLin P v = (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) •
      toEuclideanLin Q (selectedBellPost β Ω X E k) := by
  intro z ΩX J Pe P v Q
  let τ := schmidtBellWitnessEquiv β X E k
  let R := (finKronecker fun _ : Fin k ↦ selectedBellProjection ΩX E) ⊗ₖ
    (1 : Matrix (Config k ιe) (Config k ιe) ℂ)
  let Qw := (1 : Matrix L L ℂ) ⊗ₖ labelProj (subsystemPerm k ιe {none}) ell
  let post : EuclideanSpace ℂ (L × Config k ιe) := WithLp.toLp 2
    (fun x ↦ (∏ j, selectedBellVector ΩX E (x.1 j)) *
      ∏ j, compressedTypicalPureState ΩX E
        ((Finset.equivFin E).symm (x.2 j none), fun w ↦ x.2 j (some w)))
  let c : ℂ := ((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k
  have hpull (D : Matrix (L × Config k ιe) (L × Config k ιe) ℂ)
      (w : EuclideanSpace ℂ (L × Config k ιe)) :
      toEuclideanLin (D.submatrix τ τ) (WithLp.toLp 2 (w ∘ τ)) =
        WithLp.toLp 2 ((toEuclideanLin D w) ∘ τ) := by
    ext x
    simp only [toEuclideanLin, toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.submatrix_mulVec_equiv, Function.comp_def, Equiv.apply_symm_apply]
  have hraw := selectedBellProjection_replicaPrevector_site β X E k ΩX hz ell
  change toEuclideanLin R (schmidtBellSitePrevector β X E k ΩX ell) =
    c • toEuclideanLin Qw post at hraw
  have hJJ : J * Jᴴ = R.submatrix τ τ :=
    bellInsertion_mul_conjTranspose_selectedBell β X E k ΩX
  have hQ : Qw.submatrix τ τ = Q :=
    labelProj_schmidtBellWitnessEquiv_auxiliary β X E k ell
  have hpost : selectedBellPost β Ω X E k = WithLp.toLp 2 (post ∘ τ) :=
    selectedBellPost_eq_pullback β Ω X E k
  have hpin : toEuclideanLin (J * Jᴴ) v =
      c • toEuclideanLin Q (selectedBellPost β Ω X E k) := by
    rw [hJJ]
    change toEuclideanLin (R.submatrix τ τ)
      (WithLp.toLp 2 (schmidtBellSitePrevector β X E k ΩX ell ∘ τ)) = _
    rw [hpull, hraw, ← hQ, hpost, hpull]
    rfl
  let S := symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k)
  have hP : P = S * (J * Jᴴ) := by
    rw [← Matrix.mul_assoc]
    change J * Pe * Jᴴ = (S * J) * Jᴴ
    rw [symProj_mul_bellInsertion β X E (Fin E.card) k (selectedBellVector ΩX E)]
  rw [hP, toLpLin_mul_same, LinearMap.comp_apply, hpin, map_smul]
  rw [symProj_labelProj_selectedBellPost β Ω X E k ell]

end TensorPower
