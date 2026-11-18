/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Configurations of a system of sites

A system of sites assigns a basis type `X v` to every site `v : V`; it stands for the tensor
product `⊗_v ℂ^{X v}`, whose standard basis is indexed by the configurations `(v : V) → X v`.
A region is a finite set `D` of sites. Its configurations are the families `(v : D) → X v`,
and every configuration of the system is a pair of a configuration of `D` and a configuration
of the sites outside `D`.

The basis types are arbitrary. One local dimension `d` on sites `ι` is the system
`fun _ : ι ↦ Fin d`, with configurations `ι → Fin d`; site-dependent dimensions `n : V → ℕ`
are the system `fun v ↦ Fin (n v)`. Both are instances by unfolding, so a statement about a
system `X` applies to them as it stands.

## Main definitions

* `ManyBody.Config` — configurations of a system.
* `ManyBody.RegionConfig`, `ManyBody.ComplConfig` — configurations of a region and of its
  complement.
* `ManyBody.Qudits` — the system with the basis `Fin d` at every site.
* `ManyBody.cutEquiv` — a configuration as a pair of a configuration of a region and one of
  its complement.
-/

namespace ManyBody

variable {V : Type*}

/-- Configurations of a system of sites with basis types `X`: the index type of the standard
basis of `⊗_v ℂ^{X v}`. -/
abbrev Config (X : V → Type*) := (v : V) → X v

/-- The system with the basis `Fin d` at every site of `V`. -/
abbrev Qudits (V : Type) (d : ℕ) : V → Type := fun _ ↦ Fin d

/-- Configurations of a region `D`. -/
abbrev RegionConfig (X : V → Type*) (D : Finset V) := (v : {v // v ∈ D}) → X v

/-- Configurations of the sites outside a region `D`. -/
abbrev ComplConfig (X : V → Type*) (D : Finset V) := (v : {v // v ∉ D}) → X v

variable [DecidableEq V]

/-- The cut of a configuration into its parts on a region `D` and outside it. -/
abbrev cutEquiv (X : V → Type*) (D : Finset V) :
    Config X ≃ RegionConfig X D × ComplConfig X D :=
  Equiv.piEquivPiSubtypeProd (· ∈ D) X

variable {X : V → Type*} {D : Finset V}

/-- At a site of `D`, the configuration glued from `x` on `D` and `y` outside `D` takes the
value of `x`. -/
theorem cutEquiv_symm_apply_mem (x : RegionConfig X D) (y : ComplConfig X D) {v : V}
    (hv : v ∈ D) : (cutEquiv X D).symm (x, y) v = x ⟨v, hv⟩ := by
  simp [Equiv.piEquivPiSubtypeProd, hv]

/-- At a site outside `D`, the configuration glued from `x` on `D` and `y` outside `D` takes
the value of `y`. -/
theorem cutEquiv_symm_apply_not_mem (x : RegionConfig X D) (y : ComplConfig X D) {v : V}
    (hv : v ∉ D) : (cutEquiv X D).symm (x, y) v = y ⟨v, hv⟩ := by
  simp [Equiv.piEquivPiSubtypeProd, hv]

/-- Two configurations have the same part on `D` exactly when they agree on `D`. -/
theorem cutEquiv_fst_eq_iff {σ τ : Config X} :
    (cutEquiv X D σ).1 = (cutEquiv X D τ).1 ↔ ∀ v ∈ D, σ v = τ v :=
  ⟨fun h v hv ↦ congrFun h ⟨v, hv⟩, fun h ↦ funext fun v ↦ h v.1 v.2⟩

/-- Two configurations have the same part outside `D` exactly when they agree outside `D`. -/
theorem cutEquiv_snd_eq_iff {σ τ : Config X} :
    (cutEquiv X D σ).2 = (cutEquiv X D τ).2 ↔ ∀ v ∉ D, σ v = τ v :=
  ⟨fun h v hv ↦ congrFun h ⟨v, hv⟩, fun h ↦ funext fun v ↦ h v.1 v.2⟩

end ManyBody
