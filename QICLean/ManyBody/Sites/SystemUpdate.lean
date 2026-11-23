/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement

/-!
# Systems changed on a region, and placement between two systems

An operation on a region `D` may change the basis types of the sites of `D`: it prepares or
discards registers there, and leaves the other sites alone. Its input and output systems `X` and
`Y` then agree outside `D`. The system `updateOn X D Z` is `X` with the basis types `Z` on `D`;
it is one such `Y`.

For two systems `X` and `Y` that agree outside `D`, the placement `placeBetween D hXY K` of a
matrix `K` from the configurations of `D` in `X` to those in `Y` is the operator `K ⊗ 1` from
`⊗_v ℂ^{X v}` to `⊗_v ℂ^{Y v}`: it acts as `K` on the sites of `D` and as the identity on the
other sites. When `Y = X` it is the placement `place D K`. Placements on the same region compose
as their matrices do, and the adjoint of a placement is the placement of the adjoint.

The agreement outside `D` is a hypothesis `hXY : ∀ v ∉ D, Y v = X v`, not a definition of `Y`,
so that a placement from `X` to `Y` followed by one from `Y` to `W` is a placement from `X` to
`W`. The identification of the configurations outside `D` of the two systems along `hXY` is the
equivalence `complCast hXY`.

## Main definitions

* `ManyBody.updateOn` — the system `X` with the basis types `Z` on a region.
* `ManyBody.updateOnConfigEquiv` — its configurations, as pairs.
* `ManyBody.complCast` — configurations outside a region of two systems that agree there.
* `ManyBody.placeBetween` — the placement `K ⊗ 1` of a matrix between two systems.

## Main results

* `ManyBody.placeBetween_apply`, `ManyBody.placeBetween_apply_cutEquiv_symm` — its entries.
* `ManyBody.placeBetween_eq_place` — on one system it is the placement.
* `ManyBody.placeBetween_mul` — placements on a region compose.
* `ManyBody.placeBetween_conjTranspose` — the adjoint of a placement.
-/

open Matrix
open scoped Kronecker

universe u

namespace ManyBody

variable {V : Type*}

/-! ### Systems changed on a region -/

section Update

variable [DecidableEq V]

/-- The system `X` with the basis type `Z v` at every site `v` of the region `D`. -/
def updateOn (X : V → Type u) (D : Finset V) (Z : {v // v ∈ D} → Type u) : V → Type u :=
  fun v ↦ if h : v ∈ D then Z ⟨v, h⟩ else X v

variable {X : V → Type u} {D : Finset V} {Z : {v // v ∈ D} → Type u}

theorem updateOn_of_mem {v : V} (hv : v ∈ D) : updateOn X D Z v = Z ⟨v, hv⟩ := by
  simp [updateOn, hv]

theorem updateOn_of_notMem {v : V} (hv : v ∉ D) : updateOn X D Z v = X v := by
  simp [updateOn, hv]

/-- The updated system agrees with `X` outside the region, in the form `placeBetween` takes. -/
theorem updateOn_eq_of_notMem : ∀ v ∉ D, updateOn X D Z v = X v :=
  fun _ hv ↦ updateOn_of_notMem hv

instance [∀ v, Fintype (X v)] [∀ v, Fintype (Z v)] (v : V) : Fintype (updateOn X D Z v) := by
  unfold updateOn; split <;> infer_instance

instance [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (Z v)] (v : V) :
    DecidableEq (updateOn X D Z v) := by
  unfold updateOn; split <;> infer_instance

variable (X D Z) in
/-- A configuration of the updated system is a configuration of `Z` on the sites of `D` and a
configuration of `X` outside `D`. -/
def updateOnConfigEquiv : Config (updateOn X D Z) ≃ Config Z × ComplConfig X D :=
  (cutEquiv (updateOn X D Z) D).trans <|
    Equiv.prodCongr (Equiv.piCongrRight fun v ↦ Equiv.cast (updateOn_of_mem v.2))
      (Equiv.piCongrRight fun v ↦ Equiv.cast (updateOn_of_notMem v.2))

@[simp] theorem updateOnConfigEquiv_apply_fst (σ : Config (updateOn X D Z))
    (v : {v // v ∈ D}) : (updateOnConfigEquiv X D Z σ).1 v = cast (updateOn_of_mem v.2) (σ v) :=
  rfl

@[simp] theorem updateOnConfigEquiv_apply_snd (σ : Config (updateOn X D Z))
    (v : {v // v ∉ D}) :
    (updateOnConfigEquiv X D Z σ).2 v = cast (updateOn_of_notMem v.2) (σ v) :=
  rfl

end Update

/-! ### Placement between two systems -/

variable {X Y W : V → Type u} {D : Finset V}

/-- The configurations outside `D` of two systems that agree outside `D` are the same. -/
def complCast (hXY : ∀ v ∉ D, Y v = X v) : ComplConfig X D ≃ ComplConfig Y D :=
  Equiv.piCongrRight fun v ↦ Equiv.cast (hXY v v.2).symm

@[simp] theorem complCast_apply (hXY : ∀ v ∉ D, Y v = X v) (z : ComplConfig X D)
    (v : {v // v ∉ D}) : complCast hXY z v = cast (hXY v v.2).symm (z v) :=
  rfl

@[simp] theorem complCast_symm_apply (hXY : ∀ v ∉ D, Y v = X v) (z : ComplConfig Y D)
    (v : {v // v ∉ D}) : (complCast hXY).symm z v = cast (hXY v v.2) (z v) :=
  rfl

@[simp] theorem complCast_rfl : complCast (fun _ _ ↦ rfl : ∀ v ∉ D, X v = X v) = Equiv.refl _ :=
  rfl

theorem complCast_symm (hXY : ∀ v ∉ D, Y v = X v) :
    (complCast hXY).symm = complCast fun v hv ↦ (hXY v hv).symm :=
  rfl

theorem complCast_trans (hXY : ∀ v ∉ D, Y v = X v) (hYW : ∀ v ∉ D, W v = Y v) :
    (complCast hXY).trans (complCast hYW) = complCast fun v hv ↦ (hYW v hv).trans (hXY v hv) :=
  Equiv.ext fun z ↦ funext fun v ↦ by simp

variable [DecidableEq V] [Fintype V] [∀ v, DecidableEq (X v)]

variable (D) in
/-- The placement `K ⊗ 1` of a matrix `K` from the configurations of the region `D` in the
system `X` to those in a system `Y` that agrees with `X` outside `D`: the operator that acts as
`K` on the sites of `D` and as the identity on the other sites. -/
noncomputable def placeBetween (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) : Matrix (Config Y) (Config X) ℂ :=
  reindex (cutEquiv Y D).symm (cutEquiv X D).symm
    (K ⊗ₖ ((complCast hXY).symm.toPEquiv.toMatrix : Matrix (ComplConfig Y D) _ ℂ))

/-- Entries of a placement between two systems: the entry of `K` at the parts of `y` and `x` on
`D` when `y` and `x` agree outside `D`, and zero otherwise. -/
theorem placeBetween_apply (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) (y : Config Y) (x : Config X) :
    placeBetween D hXY K y x =
      if ∀ v (hv : v ∉ D), cast (hXY v hv) (y v) = x v then
        K (fun v ↦ y v) (fun v ↦ x v) else 0 := by
  simp only [placeBetween, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, mul_ite,
    mul_one, mul_zero]
  exact if_congr ⟨fun h v hv ↦ congrFun h ⟨v, hv⟩, fun h ↦ funext fun v ↦ h v.1 v.2⟩ rfl rfl

/-- A matrix on a region is recovered from its placement between two systems, at any
configuration `z` of the other sites. -/
theorem placeBetween_apply_cutEquiv_symm (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) (a : RegionConfig Y D)
    (b : RegionConfig X D) (z : ComplConfig X D) :
    placeBetween D hXY K ((cutEquiv Y D).symm (a, complCast hXY z)) ((cutEquiv X D).symm (b, z)) =
      K a b := by
  simp [placeBetween, PEquiv.toMatrix_apply]

/-- On one system, the placement between two systems is the placement. -/
theorem placeBetween_eq_place (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    placeBetween D (fun _ _ ↦ rfl) K = place D K := by
  rw [placeBetween, place, complCast_rfl, Equiv.refl_symm, Equiv.toPEquiv_refl,
    PEquiv.toMatrix_refl]

@[simp] theorem placeBetween_zero (hXY : ∀ v ∉ D, Y v = X v) :
    placeBetween D hXY (0 : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) = 0 := by
  simp [placeBetween]

theorem placeBetween_add (hXY : ∀ v ∉ D, Y v = X v)
    (K K' : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hXY (K + K') = placeBetween D hXY K + placeBetween D hXY K' := by
  simp [placeBetween, add_kronecker, submatrix_add]

theorem placeBetween_smul (hXY : ∀ v ∉ D, Y v = X v) (c : ℂ)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hXY (c • K) = c • placeBetween D hXY K := by
  simp [placeBetween, smul_kronecker, submatrix_smul]

/-- Placements on a region compose: `(K' ⊗ 1)(K ⊗ 1) = K' K ⊗ 1`. -/
theorem placeBetween_mul [∀ v, Fintype (Y v)] [∀ v, DecidableEq (Y v)]
    [Fintype (RegionConfig Y D)] (hXY : ∀ v ∉ D, Y v = X v) (hYW : ∀ v ∉ D, W v = Y v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ)
    (K' : Matrix (RegionConfig W D) (RegionConfig Y D) ℂ) :
    placeBetween D hYW K' * placeBetween D hXY K =
      placeBetween D (fun v hv ↦ (hYW v hv).trans (hXY v hv)) (K' * K) := by
  obtain rfl : ‹Fintype (RegionConfig Y D)› = Pi.instFintype := Subsingleton.elim _ _
  simp only [placeBetween, reindex_apply, Equiv.symm_symm, submatrix_mul_equiv,
    ← mul_kronecker_mul, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, ← Equiv.symm_trans,
    complCast_trans]

/-- The adjoint of a placement between two systems is the placement of the adjoint. -/
theorem placeBetween_conjTranspose [∀ v, DecidableEq (Y v)] (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    (placeBetween D hXY K)ᴴ = placeBetween D (fun v hv ↦ (hXY v hv).symm) Kᴴ := by
  have hC : ((complCast hXY).symm.toPEquiv.toMatrix : Matrix (ComplConfig Y D) _ ℂ)ᴴ =
      (complCast fun v hv ↦ (hXY v hv).symm).symm.toPEquiv.toMatrix := by
    ext a b
    simp only [conjTranspose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, apply_ite star, star_one, star_zero]
    exact if_congr ((Equiv.symm_apply_eq _).trans eq_comm) rfl rfl
  simp only [placeBetween, reindex_apply, conjTranspose_submatrix, conjTranspose_kronecker, hC]

end ManyBody
