/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.MonomialMatrix
import QICLean.ManyBody.Sites.Placement.PlaceAlong

/-!
# Placement of monomial matrices along an injection of sites

A permutation `σ` of the configurations of the sites `W`, placed along an injection
`w : W ↪ V`, is the permutation `ManyBody.placeAlongPerm w σ` of the configurations of the whole
system that replaces the values of a configuration on the image of `w` by `σ` of them and keeps
the values outside the image. A monomial matrix with permutation `σ` and phases `φ`, placed along
`w`, is the monomial matrix with this permutation and the phase `φ` of the restriction of a
configuration to the image (`ManyBody.placeAlong_monomial`). For the window of `L` consecutive
sites of a ring (`ManyBody.ringWindow`) this is the placement of a monomial operator of `L` sites
at one window of the ring.

Adapted from TNLean, `MPOTensor.windowPerm` and `MPOTensor.placeAlong_ringWindow_monomial` of
`TNLean/MPS/MPDO/EmbedLocalOperatorMonomial.lean` at commit `49b78ed821` (Apache-2.0). Changes:
any injection of sites and any finite bases instead of a window of a ring with one common basis;
the permutation is defined through the cut of the configurations along the image.

## Main definitions

* `ManyBody.placeAlongPerm` — a permutation of the configurations of `W` placed along `w`.

## Main results

* `ManyBody.placeAlongPerm_apply_apply`, `ManyBody.placeAlongPerm_apply_of_forall_ne`,
  `ManyBody.eq_placeAlongPerm_iff` — the values of the placed permutation.
* `ManyBody.placeAlong_monomial` — a placed monomial matrix is monomial.
-/

open Matrix

namespace ManyBody

variable {V : Type*} [DecidableEq V] {X : V → Type*} {W : Type*} [Fintype W] (w : W ↪ V)

/-- **A permutation placed along an injection of sites.** For a permutation `σ` of the
configurations of the sites `W`, the site `u` carrying the basis `X (w u)`, the permutation of
the configurations of the whole system that replaces the values on the image of `w` by `σ` of
them and keeps the values outside the image. -/
noncomputable def placeAlongPerm (σ : Equiv.Perm (Config fun u ↦ X (w u))) :
    Equiv.Perm (Config X) :=
  (cutEquiv X (Finset.univ.map w)).trans
    ((((windowConfigEquiv w).permCongr σ).prodCongr (Equiv.refl _)).trans
      (cutEquiv X (Finset.univ.map w)).symm)

variable {w}

/-- On the image of `w`, the placed permutation takes the values of `σ` of the restriction. -/
theorem placeAlongPerm_apply_apply (σ : Equiv.Perm (Config fun u ↦ X (w u))) (c : Config X)
    (u : W) : placeAlongPerm w σ c (w u) = σ (fun u ↦ c (w u)) u := by
  have hmem : w u ∈ Finset.univ.map w := Finset.mem_map_of_mem _ (Finset.mem_univ u)
  simp only [placeAlongPerm, Equiv.trans_apply, Equiv.prodCongr_apply]
  rw [cutEquiv_symm_apply_mem _ _ hmem]
  change windowConfigEquiv w (σ ((windowConfigEquiv w).symm fun v ↦ c v)) (windowEquiv w u) = _
  rw [windowConfigEquiv_apply_windowEquiv]
  rfl

/-- Outside the image of `w`, the placed permutation keeps the values of the configuration. -/
theorem placeAlongPerm_apply_of_forall_ne (σ : Equiv.Perm (Config fun u ↦ X (w u)))
    (c : Config X) {v : V} (hv : ∀ u, w u ≠ v) : placeAlongPerm w σ c v = c v := by
  have hnot : v ∉ Finset.univ.map w := by simpa using hv
  simp only [placeAlongPerm, Equiv.trans_apply, Equiv.prodCongr_apply]
  rw [cutEquiv_symm_apply_not_mem _ _ hnot]
  rfl

/-- A configuration is the image of `c` under the placed permutation exactly when it agrees with
`c` outside the image of `w` and its restriction to the image is `σ` of that of `c`. -/
theorem eq_placeAlongPerm_iff (σ : Equiv.Perm (Config fun u ↦ X (w u))) (c c' : Config X) :
    c' = placeAlongPerm w σ c ↔
      (∀ v, (∀ u, w u ≠ v) → c' v = c v) ∧ (fun u ↦ c' (w u)) = σ (fun u ↦ c (w u)) := by
  constructor
  · rintro rfl
    exact ⟨fun v hv ↦ placeAlongPerm_apply_of_forall_ne σ c hv,
      funext fun u ↦ placeAlongPerm_apply_apply σ c u⟩
  · rintro ⟨hout, hin⟩
    funext v
    by_cases hv : ∃ u, w u = v
    · obtain ⟨u, rfl⟩ := hv
      rw [placeAlongPerm_apply_apply, ← hin]
    · push Not at hv
      rw [placeAlongPerm_apply_of_forall_ne σ c hv, hout v hv]

variable [Fintype V] [∀ v, DecidableEq (X v)]

/-- **A placed monomial matrix is monomial.** The monomial matrix with permutation `σ` and phases
`φ` on the configurations of `W`, placed along `w`, is the monomial matrix whose permutation
replaces the values of a configuration on the image of `w` by `σ` of them and whose phase is
`φ` of the restriction of the configuration to the image. -/
theorem placeAlong_monomial (σ : Equiv.Perm (Config fun u ↦ X (w u)))
    (φ : (Config fun u ↦ X (w u)) → ℂ) :
    placeAlong w (monomial σ φ) =
      monomial (placeAlongPerm w σ) fun c ↦ φ fun u ↦ c (w u) := by
  ext t s
  rw [placeAlong_apply, monomial_apply, monomial_apply]
  simp only [eq_placeAlongPerm_iff, ite_and]

end ManyBody
