/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellWitnessCoordinates
import QICLean.Representation.GroupAlgebraProductCoordinates
import QICLean.Representation.SchurLabelCutoff

/-!
# The common Bell witness in the original physical coordinates

The selected-Bell and exterior coordinates are related to the original
physical coordinates by a fixed bijection. Pullback preserves simultaneous
copy symmetry. The selected Bell range and this symmetry together imply that
the pulled-back vector is fixed by the inserted symmetric operator.
Auxiliary labels and every exterior cutoff are transported by their actual
subsystem permutation actions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308 and 332–365,
  at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation TensorPower
open scoped BigOperators Matrix Kronecker

noncomputable section

namespace FiniteProduct

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ)

local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => compressedSiteSpace β X (Fin E.card)
local notation "L" => Fin k → A × E

local instance schmidtBellRangeConfigurationDecidableEq : DecidableEq (Configuration β X) :=
  Fintype.decidablePiFintype

local instance schmidtBellRangeOriginalConfigDecidableEq : DecidableEq (Config k ι₀) :=
  Fintype.decidablePiFintype

/-- Pullback of a vector in the selected Bell range and the simultaneous-copy
symmetric subspace is fixed by the actual inserted symmetric operator.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308 and 346–354. -/
theorem schmidtBellWitness_pullback_range
    (Ω : EuclideanSpace ℂ (A × B)) (φ : EuclideanSpace ℂ (L × Config k ιe))
    (hsym :
      let e := Equiv.arrowProdEquivProdArrow (Fin k)
        (fun _ ↦ A × E) (fun _ ↦ (f : Option ↥(Xᶜ)) → ιe f)
      (fun x ↦ φ (e x)) ∈ invariantSubspace
        (copyPerm ((A × E) × ((f : Option ↥(Xᶜ)) → ιe f)) k))
    (hBell : toEuclideanLin
      ((finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
        (1 : Matrix (Config k ιe) (Config k ιe) ℂ)) φ = φ) :
    let τ := schmidtBellWitnessEquiv β X E k
    let Φ : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2 (φ ∘ τ)
    let J := (addedSiteInsertion ιe (A × E) k (selectedBellVector Ω E)).submatrix
      (bellInsertionCopyEquiv β X ↥E (Fin E.card) k) id
    let Pe := symProj (copyPerm ((f : Option ↥(Xᶜ)) → ιe f) k)
    (fun x ↦ Φ x) ∈ symmetricSubspace k ι₀ ∧
      toEuclideanLin (J * Pe * Jᴴ) Φ = Φ := by
  classical
  intro τ Φ J Pe
  let e := Equiv.arrowProdEquivProdArrow (Fin k)
    (fun _ ↦ A × E) (fun _ ↦ (f : Option ↥(Xᶜ)) → ιe f)
  have hΦ : (fun x ↦ Φ x) ∈ symmetricSubspace k ι₀ := by
    intro σ
    funext x
    have h := congrFun (hsym σ) (e.symm (τ x))
    rw [permOp_mulVec] at h ⊢
    change φ ((fun j ↦ (τ x).1 (σ j)), (fun j ↦ (τ x).2 (σ j))) = φ (τ x) at h ⊢
    exact h
  have hJJ : (J * Jᴴ) *ᵥ (φ ∘ τ) = φ ∘ τ := by
    rw [bellInsertion_mul_conjTranspose_selectedBell β X E k Ω]
    rw [Matrix.submatrix_mulVec_equiv]
    simpa only [τ, Function.comp_def, Equiv.apply_symm_apply, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, WithLp.ofLp_toLp] using
      congrArg (fun v : EuclideanSpace ℂ (L × Config k ιe) ↦ (fun x ↦ v (τ x))) hBell
  have hPi := symProj_mul_bellInsertion β X ↥E (Fin E.card) k (selectedBellVector Ω E)
  have hP : J * Pe * Jᴴ =
      symProj (copyPerm ((f : Option (Option V)) → ι₀ f) k) * (J * Jᴴ) := by
    rw [← Matrix.mul_assoc, hPi]
  refine ⟨hΦ, ?_⟩
  apply WithLp.ofLp_injective 2
  change (J * Pe * Jᴴ) *ᵥ (φ ∘ τ) = φ ∘ τ
  rw [hP, ← Matrix.mulVec_mulVec, hJJ]
  exact symProj_mulVec_of_mem _ hΦ

/-- The original auxiliary label is the same exterior auxiliary label after
pullback of the actual witness coordinates.
Source: area-law manuscript, `07-comparators.tex`, lines 283–290 and 346–354. -/
theorem labelProj_schmidtBellWitnessEquiv_auxiliary
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    ((1 : Matrix L L ℂ) ⊗ₖ labelProj (subsystemPerm k ιe {none}) ell).submatrix
        (schmidtBellWitnessEquiv β X E k) (schmidtBellWitnessEquiv β X E k) =
      labelProj (subsystemPerm k ι₀ {none}) ell := by
  classical
  let τ := schmidtBellWitnessEquiv β X E k
  have he (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
      τ (subsystemPerm k ι₀ {none} σ x) =
        ((τ x).1, subsystemPerm k ιe {none} σ (τ x).2) := by
    apply Prod.ext
    · funext j
      apply Prod.ext
      · funext v
        change subsystemPerm k ι₀ {none} σ x j (some (some (v : V))) =
          x j (some (some (v : V)))
        simp
      · change subsystemPerm k ι₀ {none} σ x j (some none) = x j (some none)
        simp
    · funext j o
      cases o with
      | none =>
        change subsystemPerm k ι₀ {none} σ x j none =
          if none ∈ ({none} : Finset (Option ↥(Xᶜ))) then
            x (σ⁻¹ j) none else x j none
        simp
      | some v =>
        change subsystemPerm k ι₀ {none} σ x j (some (some (v : V))) =
          if some v ∈ ({none} : Finset (Option ↥(Xᶜ))) then
            x (σ⁻¹ j) (some (some (v : V))) else x j (some (some (v : V)))
        simp
  have h := groupAlgebraRep_submatrix_of_prod_action
    (subsystemPerm k ι₀ {none}) (subsystemPerm k ιe {none}) τ he
    (IrrepLabel.centralIdem ell)
  ext x y
  change ((1 : Matrix L L ℂ) ⊗ₖ
      groupAlgebraRep (subsystemPerm k ιe {none}) (IrrepLabel.centralIdem ell)) (τ x) (τ y) =
    groupAlgebraRep (subsystemPerm k ι₀ {none}) (IrrepLabel.centralIdem ell) x y
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using
    (congrArg (fun M ↦ M (τ x) (τ y)) h).symm

/-- Each physical exterior cutoff, with its original threshold, is the
pullback of the same cutoff in witness coordinates.
Source: area-law manuscript, `07-comparators.tex`, lines 346–365. -/
theorem labelCutoff_schmidtBellWitnessEquiv_exterior (U : Finset V) (a : ℝ) :
    ((1 : Matrix L L ℂ) ⊗ₖ
      labelCutoff (subsystemPerm k ιe (exteriorRegion X U)) a).submatrix
        (schmidtBellWitnessEquiv β X E k) (schmidtBellWitnessEquiv β X E k) =
      labelCutoff (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v))) a := by
  classical
  let τ := schmidtBellWitnessEquiv β X E k
  let q := exteriorRegion X U
  have he (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
      τ (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)) σ x) =
        ((τ x).1, subsystemPerm k ιe q σ (τ x).2) := by
    change addedSiteConfigEquiv ιe (A × E) k
      (bellInsertionCopyEquiv β X ↥E (Fin E.card) k
        (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)) σ x)) = _
    rw [bellInsertionCopyEquiv_subsystemPerm_exterior]
    let y := bellInsertionCopyEquiv β X ↥E (Fin E.card) k x
    apply Prod.ext
    · funext j
      change (if none ∈ q.image some then y (σ⁻¹ j) none else y j none) = y j none
      simp
    · funext j o
      change (if some o ∈ q.image some then y (σ⁻¹ j) (some o) else y j (some o)) =
        if o ∈ q then y (σ⁻¹ j) (some o) else y j (some o)
      simp
  rw [labelCutoff, labelCutoff, labelObservable_eq_groupAlgebraRep,
    labelObservable_eq_groupAlgebraRep]
  have h := groupAlgebraRep_submatrix_of_prod_action
    (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)))
    (subsystemPerm k ιe q) τ he
    (∑ l, ((if Real.log l.dim ≤ a then 1 else 0 : ℝ) : ℂ) • IrrepLabel.centralIdem l)
  ext x y
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using
    (congrArg (fun M ↦ M (τ x) (τ y)) h).symm

end FiniteProduct
