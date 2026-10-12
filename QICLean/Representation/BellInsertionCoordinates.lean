/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.AddedSiteTensorInsertion
import QICLean.Entropy.CompressedSiteCoordinates
import QICLean.Channel.FiniteProduct

/-!
# Physical Bell coordinates and the actual insertion

In the original site family the two auxiliary sites carry R and C. We group
C with the original physical coordinates in X, leaving R and the physical
complement as the exterior site family. The equivalence below retains each
coordinate literally; C and R may be different types.

Permuting C together with X ∪ U becomes permutation of the bundled Bell site
together with the exterior part of U. Permuting only U \ X becomes permutation
of that exterior part, fixing the Bell site. Both identities hold for arbitrary
U. They extend to every real function of the same irreducible label and hence
to the actual insertion of any Bell-coordinate vector.

In particular, a replica-metric application uses the weights of the original
full family on both sides. No equality with weights recomputed from the
compressed family is asserted. No normalization, nonzero coordinate space,
state identity, or supplied intertwining assumption is needed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308,
  `comparator:bell-pin` and `comparator:pinned-metric`, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ι₁" => addedSiteSpace (compressedSiteSpace β X R) (Configuration β X × C)

/-- Group the original X coordinates and C into the Bell coordinate, retaining
R and each original complementary coordinate separately.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
def bellInsertionSiteEquiv : ((v : Option (Option V)) → ι₀ v) ≃
    ((v : Option (Option ↥(Xᶜ))) → ι₁ v) where
  toFun x o := match o with
    | none => (fun v ↦ x (some (some v)), x (some none))
    | some none => x none
    | some (some v) => x (some (some v))
  invFun y o := match o with
    | none => y (some none)
    | some none => (y none).2
    | some (some v) =>
      (FiniteProduct.splitEquiv β X).symm ((y none).1, fun w ↦ y (some (some w))) v
  left_inv x := by
    funext o
    cases o with
    | none => rfl
    | some o =>
      cases o with
      | none => rfl
      | some v =>
        exact congrFun ((FiniteProduct.splitEquiv β X).symm_apply_apply
          (fun w ↦ x (some (some w)))) v
  right_inv y := by
    funext o
    cases o with
    | none =>
      apply Prod.ext
      · funext v
        exact FiniteProduct.splitEquiv_symm_apply_of_mem β X (y none).1
          (fun w ↦ y (some (some w))) v v.property
      · rfl
    | some o =>
      cases o with
      | none => rfl
      | some v =>
        exact FiniteProduct.splitEquiv_symm_apply_of_notMem β X (y none).1
          (fun w ↦ y (some (some w))) v (Finset.mem_compl.mp v.property)

/-- Apply the physical Bell-coordinate equivalence independently to each copy.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
def bellInsertionCopyEquiv (k : ℕ) : Config k ι₀ ≃ Config k ι₁ :=
  Equiv.piCongrRight fun _ : Fin k ↦ bellInsertionSiteEquiv β X C R

/-- The actual C ∪ X ∪ U permutation becomes the permutation of the bundled
Bell coordinate and the exterior part of U. No disjointness is necessary for
this coordinate identity.
Source: area-law manuscript, `07-comparators.tex`, lines 290–308. -/
theorem bellInsertionCopyEquiv_subsystemPerm_withPin (k : ℕ) (U : Finset V)
    (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
    bellInsertionCopyEquiv β X C R k
      (subsystemPerm k ι₀
        (insert (some none) ((X ∪ U).image fun v ↦ some (some v))) σ x) =
      subsystemPerm k ι₁ (insert none ((exteriorRegion X U).image some)) σ
        (bellInsertionCopyEquiv β X C R k x) := by
  funext j o
  cases o with
  | none =>
    change ((fun v : X ↦ subsystemPerm k ι₀
        (insert (some none) ((X ∪ U).image fun v ↦ some (some v))) σ x j
          (some (some v))),
        subsystemPerm k ι₀
          (insert (some none) ((X ∪ U).image fun v ↦ some (some v))) σ x j
            (some none)) =
      if none ∈ insert none ((exteriorRegion X U).image some) then
        (fun v : X ↦ x (σ⁻¹ j) (some (some v)), x (σ⁻¹ j) (some none)) else
        (fun v : X ↦ x j (some (some v)), x j (some none))
    rw [ite_eq_left (Finset.mem_insert_self _ _)]
    apply Prod.ext
    · funext v
      simp [subsystemPerm_apply, Finset.mem_image, v.property]
    · simp [subsystemPerm_apply]
  | some o =>
    cases o with
    | none =>
      change (if none ∈ insert (some none)
          ((X ∪ U).image fun v ↦ some (some v)) then x (σ⁻¹ j) none else x j none) =
        if some none ∈ insert none ((exteriorRegion X U).image some) then
          x (σ⁻¹ j) none else x j none
      simp [exteriorRegion, Finset.mem_image]
    | some v =>
      change (if some (some (v : V)) ∈ insert (some none)
          ((X ∪ U).image fun v ↦ some (some v)) then
            x (σ⁻¹ j) (some (some v)) else x j (some (some v))) =
        if some (some v) ∈ insert none ((exteriorRegion X U).image some) then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))
      by_cases hv : (v : V) ∈ U <;>
        simp [exteriorRegion, Finset.mem_image, Finset.mem_compl.mp v.property, hv]

/-- Permuting the original exterior part of U leaves both the bundled Bell
coordinate and R fixed. Source: area-law manuscript, `07-comparators.tex`,
lines 300–308; the Y factors in `comparator:pinned-metric`. -/
theorem bellInsertionCopyEquiv_subsystemPerm_exterior (k : ℕ) (U : Finset V)
    (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
    bellInsertionCopyEquiv β X C R k
      (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)) σ x) =
      subsystemPerm k ι₁ ((exteriorRegion X U).image some) σ
        (bellInsertionCopyEquiv β X C R k x) := by
  funext j o
  cases o with
  | none =>
    change ((fun v : X ↦ subsystemPerm k ι₀
        ((U \ X).image fun v ↦ some (some v)) σ x j (some (some v))),
        subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)) σ x j
          (some none)) =
      if none ∈ (exteriorRegion X U).image some then
        (fun v : X ↦ x (σ⁻¹ j) (some (some v)), x (σ⁻¹ j) (some none)) else
        (fun v : X ↦ x j (some (some v)), x j (some none))
    rw [ite_eq_right (by simp)]
    apply Prod.ext
    · funext v
      simp [subsystemPerm_apply, Finset.mem_image, v.property]
    · simp [subsystemPerm_apply, Finset.mem_image]
  | some o =>
    cases o with
    | none =>
      change (if none ∈ (U \ X).image (fun v ↦ some (some v)) then
          x (σ⁻¹ j) none else x j none) =
        if some none ∈ (exteriorRegion X U).image some then
          x (σ⁻¹ j) none else x j none
      simp [exteriorRegion, Finset.mem_image]
    | some v =>
      change (if some (some (v : V)) ∈ (U \ X).image (fun v ↦ some (some v)) then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))) =
        if some (some v) ∈ (exteriorRegion X U).image some then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))
      by_cases hv : (v : V) ∈ U <;>
        simp [exteriorRegion, Finset.mem_image, Finset.mem_compl.mp v.property, hv]

variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance : DecidableEq (Configuration β X) :=
  Fintype.decidablePiFintype

/-- Transport the same label function along a literal equivariant change of
finite configurations. -/
private theorem labelObservable_submatrix_of_action
    {G A B : Type*} [Group G] [Fintype G]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (φ : G →* Equiv.Perm A) (ψ : G →* Equiv.Perm B) (e : A ≃ B)
    (he : ∀ g x, e (φ g x) = ψ g (e x)) (f : IrrepLabel G → ℝ) :
    (labelObservable ψ f).submatrix e e = labelObservable φ f := by
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep,
    groupAlgebraRep_of_intertwine e (fun g x ↦ (he g x).symm)]
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- The same label function on C ∪ X ∪ U is the pulled-back label function
on the Bell site together with the exterior part of U.
Source: area-law manuscript, `07-comparators.tex`, lines 290–308. -/
theorem labelObservable_bellInsertionCopyEquiv_withPin (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    (labelObservable
        (subsystemPerm k ι₁ (insert none ((exteriorRegion X U).image some))) f).submatrix
        (bellInsertionCopyEquiv β X C R k) (bellInsertionCopyEquiv β X C R k) =
      labelObservable (subsystemPerm k ι₀
        (insert (some none) ((X ∪ U).image fun v ↦ some (some v)))) f :=
  labelObservable_submatrix_of_action _ _ _
    (bellInsertionCopyEquiv_subsystemPerm_withPin β X C R k U) f

/-- The same exterior label function is pulled back without including the
Bell site. Source: area-law manuscript, `07-comparators.tex`, lines 300–308. -/
theorem labelObservable_bellInsertionCopyEquiv_exterior (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    (labelObservable (subsystemPerm k ι₁ ((exteriorRegion X U).image some)) f).submatrix
        (bellInsertionCopyEquiv β X C R k) (bellInsertionCopyEquiv β X C R k) =
      labelObservable (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v))) f :=
  labelObservable_submatrix_of_action _ _ _
    (bellInsertionCopyEquiv_subsystemPerm_exterior β X C R k U) f

/-- Inserting a Bell-coordinate tensor power in the original physical
coordinates intertwines the actual C ∪ X ∪ U operator with the exterior U
operator, for exactly the same label function.
Source: area-law manuscript, `07-comparators.tex`, lines 290–308. -/
theorem labelObservable_mul_bellInsertion_withPin (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : Configuration β X × C → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion (compressedSiteSpace β X R) (Configuration β X × C) k b).submatrix
      e id
    labelObservable (subsystemPerm k ι₀
        (insert (some none) ((X ∪ U).image fun v ↦ some (some v)))) f * J =
      J * labelObservable (subsystemPerm k (compressedSiteSpace β X R)
        (exteriorRegion X U)) f := by
  intro e J
  rw [← labelObservable_bellInsertionCopyEquiv_withPin β X C R k U f]
  change (labelObservable
      (subsystemPerm k ι₁ (insert none ((exteriorRegion X U).image some))) f).submatrix e e *
      (addedSiteInsertion (compressedSiteSpace β X R) (Configuration β X × C) k b).submatrix
      e id = _
  rw [Matrix.submatrix_mul_equiv, labelObservable_mul_addedSiteInsertion]
  exact Matrix.submatrix_mul _ _ e id id Function.bijective_id

/-- The same inserted vector also intertwines the original exterior operator;
the Bell and R coordinates are fixed. The label function remains unchanged.
Source: area-law manuscript, `07-comparators.tex`, lines 300–308. -/
theorem labelObservable_mul_bellInsertion_exterior (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : Configuration β X × C → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion (compressedSiteSpace β X R) (Configuration β X × C) k b).submatrix
      e id
    labelObservable (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v))) f * J =
      J * labelObservable (subsystemPerm k (compressedSiteSpace β X R)
        (exteriorRegion X U)) f := by
  intro e J
  rw [← labelObservable_bellInsertionCopyEquiv_exterior β X C R k U f]
  change (labelObservable (subsystemPerm k ι₁ ((exteriorRegion X U).image some)) f).submatrix e e *
      (addedSiteInsertion (compressedSiteSpace β X R) (Configuration β X × C) k b).submatrix
      e id = _
  rw [Matrix.submatrix_mul_equiv, labelObservable_mul_addedSiteInsertion_exterior]
  exact Matrix.submatrix_mul _ _ e id id Function.bijective_id

end TensorPower
