/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.AddedSite.TensorInsertion
import QICLean.ManyBody.Sites.CompressedSiteCoordinates
import QICLean.ManyBody.Sites.RegionMatrix

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

open Matrix PermutationRepresentation
open scoped BigOperators

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ι₁" => addedSiteSpace (ManyBody.compressedSiteSpace β X R)
    (ManyBody.RegionConfig β X × C)

/-- Group the original X coordinates and C into the Bell coordinate, retaining
R and each original complementary coordinate separately.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
def bellInsertionSiteEquiv : ((v : Option (Option V)) → ι₀ v) ≃
    ((v : Option (Option {v // v ∉ X})) → ι₁ v) where
  toFun x o := match o with
    | none => (fun v ↦ x (some (some v)), x (some none))
    | some none => x none
    | some (some v) => x (some (some v))
  invFun y o := match o with
    | none => y (some none)
    | some none => (y none).2
    | some (some v) =>
      (ManyBody.cutEquiv β X).symm ((y none).1, fun w ↦ y (some (some w))) v
  left_inv x := by
    funext o
    cases o with
    | none => rfl
    | some o =>
      cases o with
      | none => rfl
      | some v =>
        exact congrFun ((ManyBody.cutEquiv β X).symm_apply_apply
          (fun w ↦ x (some (some w)))) v
  right_inv y := by
    funext o
    cases o with
    | none =>
      apply Prod.ext
      · funext v
        exact ManyBody.cutEquiv_symm_apply_mem (y none).1
          (fun w ↦ y (some (some w))) v.property
      · rfl
    | some o =>
      cases o with
      | none => rfl
      | some v =>
        exact ManyBody.cutEquiv_symm_apply_not_mem (y none).1
          (fun w ↦ y (some (some w))) v.property

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
      subsystemPerm k ι₁ (insert none ((ManyBody.exteriorRegion X U).image some)) σ
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
      if none ∈ insert none ((ManyBody.exteriorRegion X U).image some) then
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
        if some none ∈ insert none ((ManyBody.exteriorRegion X U).image some) then
          x (σ⁻¹ j) none else x j none
      simp [ManyBody.exteriorRegion, Finset.mem_image]
    | some v =>
      change (if some (some (v : V)) ∈ insert (some none)
          ((X ∪ U).image fun v ↦ some (some v)) then
            x (σ⁻¹ j) (some (some v)) else x j (some (some v))) =
        if some (some v) ∈ insert none ((ManyBody.exteriorRegion X U).image some) then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))
      by_cases hv : (v : V) ∈ U <;>
        simp [ManyBody.exteriorRegion, Finset.mem_image, v.property, hv]

/-- Permuting the original exterior part of U leaves both the bundled Bell
coordinate and R fixed. Source: area-law manuscript, `07-comparators.tex`,
lines 300–308; the Y factors in `comparator:pinned-metric`. -/
theorem bellInsertionCopyEquiv_subsystemPerm_exterior (k : ℕ) (U : Finset V)
    (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
    bellInsertionCopyEquiv β X C R k
      (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)) σ x) =
      subsystemPerm k ι₁ ((ManyBody.exteriorRegion X U).image some) σ
        (bellInsertionCopyEquiv β X C R k x) := by
  funext j o
  cases o with
  | none =>
    change ((fun v : X ↦ subsystemPerm k ι₀
        ((U \ X).image fun v ↦ some (some v)) σ x j (some (some v))),
        subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v)) σ x j
          (some none)) =
      if none ∈ (ManyBody.exteriorRegion X U).image some then
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
        if some none ∈ (ManyBody.exteriorRegion X U).image some then
          x (σ⁻¹ j) none else x j none
      simp [ManyBody.exteriorRegion, Finset.mem_image]
    | some v =>
      change (if some (some (v : V)) ∈ (U \ X).image (fun v ↦ some (some v)) then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))) =
        if some (some v) ∈ (ManyBody.exteriorRegion X U).image some then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v))
      by_cases hv : (v : V) ∈ U <;>
        simp [ManyBody.exteriorRegion, Finset.mem_image, v.property, hv]

variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance : DecidableEq (ManyBody.RegionConfig β X) :=
  Fintype.decidablePiFintype

-- `inferInstance` for `DecidableEq (Config k ι₁)` exceeds the instance size limit otherwise.
local instance : Fintype {v // v ∉ X} := inferInstance

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
        (subsystemPerm k ι₁ (insert none ((ManyBody.exteriorRegion X U).image some))) f).submatrix
        (bellInsertionCopyEquiv β X C R k) (bellInsertionCopyEquiv β X C R k) =
      labelObservable (subsystemPerm k ι₀
        (insert (some none) ((X ∪ U).image fun v ↦ some (some v)))) f :=
  labelObservable_submatrix_of_action _ _ _
    (bellInsertionCopyEquiv_subsystemPerm_withPin β X C R k U) f

/-- The same exterior label function is pulled back without including the
Bell site. Source: area-law manuscript, `07-comparators.tex`, lines 300–308. -/
theorem labelObservable_bellInsertionCopyEquiv_exterior (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    (labelObservable (subsystemPerm k ι₁ ((ManyBody.exteriorRegion X U).image some)) f).submatrix
        (bellInsertionCopyEquiv β X C R k) (bellInsertionCopyEquiv β X C R k) =
      labelObservable (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v))) f :=
  labelObservable_submatrix_of_action _ _ _
    (bellInsertionCopyEquiv_subsystemPerm_exterior β X C R k U) f

/-- Inserting a Bell-coordinate tensor power in the original physical
coordinates intertwines the actual C ∪ X ∪ U operator with the exterior U
operator, for exactly the same label function.
Source: area-law manuscript, `07-comparators.tex`, lines 290–308. -/
theorem labelObservable_mul_bellInsertion_withPin (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : ManyBody.RegionConfig β X × C → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J :=
        (addedSiteInsertion (ManyBody.compressedSiteSpace β X R)
        (ManyBody.RegionConfig β X × C) k b).submatrix
      e id
    labelObservable (subsystemPerm k ι₀
        (insert (some none) ((X ∪ U).image fun v ↦ some (some v)))) f * J =
      J * labelObservable (subsystemPerm k (ManyBody.compressedSiteSpace β X R)
        (ManyBody.exteriorRegion X U)) f := by
  intro e J
  rw [← labelObservable_bellInsertionCopyEquiv_withPin β X C R k U f]
  change (labelObservable
      (subsystemPerm k ι₁ (insert none ((ManyBody.exteriorRegion X U).image some)))
          f).submatrix e e *
      (addedSiteInsertion (ManyBody.compressedSiteSpace β X R)
          (ManyBody.RegionConfig β X × C) k b).submatrix
      e id = _
  rw [Matrix.submatrix_mul_equiv, labelObservable_mul_addedSiteInsertion]
  exact Matrix.submatrix_mul _ _ e id id Function.bijective_id

/-- The same inserted vector also intertwines the original exterior operator;
the Bell and R coordinates are fixed. The label function remains unchanged.
Source: area-law manuscript, `07-comparators.tex`, lines 300–308. -/
theorem labelObservable_mul_bellInsertion_exterior (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : ManyBody.RegionConfig β X × C → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J :=
        (addedSiteInsertion (ManyBody.compressedSiteSpace β X R)
        (ManyBody.RegionConfig β X × C) k b).submatrix
      e id
    labelObservable (subsystemPerm k ι₀ ((U \ X).image fun v ↦ some (some v))) f * J =
      J * labelObservable (subsystemPerm k (ManyBody.compressedSiteSpace β X R)
        (ManyBody.exteriorRegion X U)) f := by
  intro e J
  rw [← labelObservable_bellInsertionCopyEquiv_exterior β X C R k U f]
  change
      (labelObservable
      (subsystemPerm k ι₁ ((ManyBody.exteriorRegion X U).image some)) f).submatrix e e *
      (addedSiteInsertion (ManyBody.compressedSiteSpace β X R)
          (ManyBody.RegionConfig β X × C) k b).submatrix
      e id = _
  rw [Matrix.submatrix_mul_equiv, labelObservable_mul_addedSiteInsertion_exterior]
  exact Matrix.submatrix_mul _ _ e id id Function.bijective_id

end TensorPower

section BellInsertionRegisterCoordinates

/-!
# Changes of coordinates in the inserted register

Changing the coordinate values at each site commutes with every subsystem
copy permutation. For Bell insertion, an equivalence of the inserted register
changes only the rows of the insertion matrix; the physical complement and
the retained auxiliary register are fixed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, lines 24–27, and
  `07-comparators.tex`, lines 283–308, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe v w

namespace TensorPower

/-- Changing coordinate values at fixed sites commutes with each subsystem
copy permutation. No finiteness or nonemptiness of the coordinate types is
needed for this identity. Source: area-law manuscript, `05-replicas.tex`,
lines 24--27, and `07-comparators.tex`, lines 283--308. -/
theorem subsystemPerm_piCongrRight
    {F : Type u} [DecidableEq F] (ι : F → Type v) (κ : F → Type w)
    (c : ∀ f, κ f ≃ ι f) (k : ℕ) (Q : Finset F)
    (σ : Equiv.Perm (Fin k)) (x : Config k κ) :
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight c
    e (subsystemPerm k κ Q σ x) = subsystemPerm k ι Q σ (e x) := by
  intro e
  funext j f
  simp only [e, Equiv.piCongrRight_apply, Pi.map_apply, subsystemPerm_apply, apply_ite]
  exact if hf : f ∈ Q then by simp only [hf, ite_true]
    else by simp only [hf, ite_false]

/-- Enumerating C changes only the rows of the actual Bell insertion. The
exterior columns and the original R register remain fixed. Source:
area-law manuscript, `07-comparators.tex`, lines 283--308. -/
theorem bellInsertion_submatrix_C_equiv
    {V : Type u} [DecidableEq V]
    (β : V → Type u)
    (X : Finset V) (C D R : Type u)
    (c : D ≃ C) (k : ℕ) (b : ManyBody.RegionConfig β X × C → ℂ) :
    let ιC := addedSiteSpace (addedSiteSpace β C) R
    let ιD := addedSiteSpace (addedSiteSpace β D) R
    let changeSite : ∀ o : Option (Option V), ιD o ≃ ιC o := fun o ↦
      match o with
      | none => Equiv.refl R
      | some none => c
      | some (some v) => Equiv.refl (β v)
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight changeSite
    let exterior := ManyBody.compressedSiteSpace β X R
    let JC := (addedSiteInsertion exterior (ManyBody.RegionConfig β X × C) k b).submatrix
      (bellInsertionCopyEquiv β X C R k) id
    let JD := (addedSiteInsertion exterior (ManyBody.RegionConfig β X × D) k
      (fun x ↦ b (x.1, c x.2))).submatrix (bellInsertionCopyEquiv β X D R k) id
    JD = JC.submatrix e id := by
  intro ιC ιD changeSite e exterior JC JD
  ext x y
  dsimp only [JD, JC, Matrix.submatrix_apply, addedSiteInsertion]
  simp only [bellInsertionCopyEquiv, Equiv.piCongrRight_apply, Pi.map_apply,
    bellInsertionSiteEquiv, Equiv.coe_fn_mk, e, changeSite, id_eq]
  dsimp only [Equiv.piCongrRight, Equiv.refl, Pi.map]
  simp only [Equiv.coe_fn_mk, Pi.map_apply]
  congr 1
  congr 2
  exact funext fun j ↦ funext fun
    | none => rfl
    | some v => rfl

end TensorPower

end BellInsertionRegisterCoordinates
