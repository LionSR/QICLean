/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionCoordinates
import QICLean.Representation.AddedSiteTensorInsertionNorm
import QICLean.Representation.AddedSiteTensorInsertionSymmetry

/-!
# Norm, copy symmetry, and the retained auxiliary label in physical Bell coordinates

The insertion is the literal tensor-power insertion of the Bell-coordinate
vector, with its rows transported to the original physical site family by
`bellInsertionCopyEquiv`. A unit inserted vector gives an isometry. The same
map intertwines simultaneous copy permutations and their averaging projections.
It also intertwines the original auxiliary R label with that of the retained
auxiliary R site, for every real function of the same irreducible label.

The coordinate spaces C and R are independent types: the original C coordinate
is bundled with the physical X coordinates, whereas R remains an exterior
site. No equality between these coordinate sets, supplied intertwining,
symmetry, or nonempty-coordinate hypothesis is used. Zero copies are included.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, lines 14–27, and
  `07-comparators.tex`, lines 283–308 and 334–354, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => compressedSiteSpace β X R
local notation "A" => Configuration β X × C
local notation "ι₁" => addedSiteSpace ιe A

/-- Grouping each copy separately commutes with simultaneous copy permutations. -/
private theorem bellInsertionCopyEquiv_copyPerm (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
    bellInsertionCopyEquiv β X C R k (copyPerm ((v : Option (Option V)) → ι₀ v) k σ x) =
      copyPerm ((v : Option (Option ↥(Xᶜ))) → ι₁ v) k σ
        (bellInsertionCopyEquiv β X C R k x) := by
  funext j
  rfl

/-- The original R site becomes the retained R site, not the bundled Bell site. -/
private theorem bellInsertionCopyEquiv_subsystemPerm_auxiliary (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
    bellInsertionCopyEquiv β X C R k
      (subsystemPerm k ι₀ {none} σ x) =
      subsystemPerm k ι₁ {some none} σ (bellInsertionCopyEquiv β X C R k x) := by
  funext j o
  cases o with
  | none =>
    change ((fun v : X ↦ subsystemPerm k ι₀ {none} σ x j (some (some v))),
        subsystemPerm k ι₀ {none} σ x j (some none)) =
      if none ∈ ({some none} : Finset (Option (Option ↥(Xᶜ)))) then
        (fun v : X ↦ x (σ⁻¹ j) (some (some v)), x (σ⁻¹ j) (some none)) else
        (fun v : X ↦ x j (some (some v)), x j (some none))
    rw [ite_eq_right (by simp)]
    apply Prod.ext
    · funext v
      simp [subsystemPerm_apply]
    · simp [subsystemPerm_apply]
  | some o =>
    cases o with
    | none =>
      change (if none ∈ ({none} : Finset (Option (Option V))) then
          x (σ⁻¹ j) none else x j none) =
        if some none ∈ ({some none} : Finset (Option (Option ↥(Xᶜ)))) then
          x (σ⁻¹ j) none else x j none
      simp
    | some v =>
      change (if some (some (v : V)) ∈ ({none} : Finset (Option (Option V))) then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))) =
        if some (some v) ∈ ({some none} : Finset (Option (Option ↥(Xᶜ)))) then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))
      simp

variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance : DecidableEq (Configuration β X) :=
  Fintype.decidablePiFintype

omit [DecidableEq C] in
/-- The literal Bell insertion in original physical coordinates is an isometry
when its inserted one-copy vector is a unit vector.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem isIsometry_bellInsertion (k : ℕ) (b : A → ℂ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) :
    let e := bellInsertionCopyEquiv β X C R k
    Matrix.IsIsometry ((addedSiteInsertion ιe A k b).submatrix e id) := by
  intro e
  exact Matrix.IsIsometry.reindex _
    (isIsometry_addedSiteInsertion ιe A k b hb) e.symm (Equiv.refl _)

/-- The actual Bell insertion intertwines simultaneous copy permutations of
its original physical and compressed exterior coordinates.
Source: area-law manuscript, `05-replicas.tex`, lines 14–27, and
`07-comparators.tex`, lines 283–308. -/
theorem permOp_copyPerm_mul_bellInsertion (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (b : A → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe A k b).submatrix e id
    permOp (copyPerm ((v : Option (Option V)) → ι₀ v) k) σ * J =
      J * permOp (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k) σ := by
  intro e J
  have hpull : (permOp (copyPerm ((v : Option (Option ↥(Xᶜ))) → ι₁ v) k) σ).submatrix
      e e = permOp (copyPerm ((v : Option (Option V)) → ι₀ v) k) σ := by
    rw [permOp_of_intertwine e
      (fun τ x ↦ (bellInsertionCopyEquiv_copyPerm β X C R k τ x).symm)]
    ext x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← hpull]
  change (permOp (copyPerm ((v : Option (Option ↥(Xᶜ))) → ι₁ v) k) σ).submatrix e e *
    (addedSiteInsertion ιe A k b).submatrix e id = _
  rw [Matrix.submatrix_mul_equiv, permOp_copyPerm_mul_addedSiteInsertion]
  exact Matrix.submatrix_mul _ _ e id id Function.bijective_id

/-- The actual Bell insertion intertwines the averaging projections onto the
simultaneous-copy symmetric subspaces. No norm condition is required.
Source: area-law manuscript, `05-replicas.tex`, lines 14–27, and
`07-comparators.tex`, lines 283–308 and 334–354. -/
theorem symProj_mul_bellInsertion (k : ℕ) (b : A → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe A k b).submatrix e id
    symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k) * J =
      J * symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k) := by
  intro e J
  dsimp only [J, e]
  simp only [symProj, Matrix.smul_mul, Matrix.mul_smul, Matrix.sum_mul,
    Matrix.mul_sum, permOp_copyPerm_mul_bellInsertion β X C R]

/-- The auxiliary R observable intertwines through the actual Bell insertion
for the same arbitrary label function on both sides. The C coordinate belongs
to the inserted Bell vector and is not identified with R.
Source: area-law manuscript, `07-comparators.tex`, `comparator:bell-pin`,
lines 283–308 and 334–354. -/
theorem labelObservable_mul_bellInsertion_auxiliary (k : ℕ)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : A → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe A k b).submatrix e id
    labelObservable (subsystemPerm k ι₀ {none}) f * J =
      J * labelObservable (subsystemPerm k ιe {none}) f := by
  intro e J
  have hpull : (labelObservable (subsystemPerm k ι₁ {some none}) f).submatrix
      e e = labelObservable (subsystemPerm k ι₀ {none}) f := by
    rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep,
      groupAlgebraRep_of_intertwine e
        (fun σ x ↦ (bellInsertionCopyEquiv_subsystemPerm_auxiliary β X C R k σ x).symm)]
    ext x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← hpull]
  change (labelObservable (subsystemPerm k ι₁ {some none}) f).submatrix e e *
    (addedSiteInsertion ιe A k b).submatrix e id = _
  have haux : ({none} : Finset (Option ↥(Xᶜ))).image some = {some none} := by simp
  rw [← haux, Matrix.submatrix_mul_equiv,
    labelObservable_mul_addedSiteInsertion_exterior]
  exact Matrix.submatrix_mul _ _ e id id Function.bijective_id

end TensorPower
