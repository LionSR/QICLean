/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Relabel

/-!
# A group acting on identical sites

A group `G` acting on the sites `V` of identical sites with basis `α` acts on the
configurations through `sitePermOp (MulAction.toPerm g)`, which maps a vector `ψ` to
`σ ↦ ψ (v ↦ σ (g • v))`. An operator is **site-invariant** when it commutes with every such
operator.

* `sitePermOp_toPerm_mul`: `g ↦ sitePermOp (MulAction.toPerm g)` is multiplicative.
* `IsSiteInvariant G H` and `isSiteInvariant_of_conj`.
* `isSiteInvariant_sum_of_covariant`: the sum of covariant terms is invariant;
  `isSiteInvariant_sum_conj` is the sum of the translates of one term.

For the translations of a lattice this is the translation invariance of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1613.

Moved from TNLean (`e113e005`): `TNLean/Lattice/SiteSymmetry.lean`. Changes: namespace `ManyBody`;
the site permutation `sitePermMatrix q g` is `sitePermOp (MulAction.toPerm g)`, for any finite
basis `α` in place of `Fin q`; its covariance is that of `Sites/Relabel`.
-/

open Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
  {G : Type*} [Group G] [MulAction G V]

omit [DecidableEq V] [Fintype α] in
theorem sitePermOp_toPerm_one :
    sitePermOp (α := α) (MulAction.toPerm (1 : G) : Equiv.Perm V) = 1 := by
  rw [show (MulAction.toPerm (1 : G) : Equiv.Perm V) = 1 from map_one (MulAction.toPermHom G V),
    sitePermOp_one]

/-- The site action is multiplicative. Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem sitePermOp_toPerm_mul (g h : G) :
    sitePermOp (α := α) (MulAction.toPerm (g * h) : Equiv.Perm V) =
      sitePermOp (MulAction.toPerm g) * sitePermOp (MulAction.toPerm h) := by
  rw [sitePermOp_mul, show (MulAction.toPerm (g * h) : Equiv.Perm V) =
    MulAction.toPerm g * MulAction.toPerm h from map_mul (MulAction.toPermHom G V) g h]

omit [DecidableEq V] [Fintype α] in
/-- The site permutation of `g⁻¹` is the adjoint of that of `g`. -/
theorem sitePermOp_toPerm_inv (g : G) :
    sitePermOp (α := α) (MulAction.toPerm g⁻¹ : Equiv.Perm V) =
      (sitePermOp (MulAction.toPerm g))ᴴ := by
  rw [conjTranspose_sitePermOp, show (MulAction.toPerm g⁻¹ : Equiv.Perm V) =
    (MulAction.toPerm g)⁻¹ from map_inv (MulAction.toPermHom G V) g]

variable (G) in
/-- An operator `H` on the configurations of identical sites is **invariant under the site
action** of `G` when it commutes with every site permutation. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1613 ("the Hamiltonian is invariant under
translation"). -/
def IsSiteInvariant (H : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) : Prop :=
  ∀ g : G, Commute (sitePermOp (MulAction.toPerm g)) H

/-- An operator with `P_g H P_g† = H` for every `g` is invariant under the site action. -/
theorem isSiteInvariant_of_conj {H : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (h : ∀ g : G, sitePermOp (MulAction.toPerm g) * H * (sitePermOp (MulAction.toPerm g))ᴴ = H) :
    IsSiteInvariant G H := fun g ↦ by
  have hu : (sitePermOp (α := α) (MulAction.toPerm g : Equiv.Perm V))ᴴ *
      sitePermOp (MulAction.toPerm g) = 1 := by
    rw [conjTranspose_sitePermOp, sitePermOp_mul, inv_mul_cancel, sitePermOp_one]
  calc sitePermOp (MulAction.toPerm g) * H
      = sitePermOp (MulAction.toPerm g) * H *
          ((sitePermOp (MulAction.toPerm g))ᴴ * sitePermOp (MulAction.toPerm g)) := by
        rw [hu, Matrix.mul_one]
    _ = H * sitePermOp (MulAction.toPerm g) := by rw [← Matrix.mul_assoc, h g]

/-- **The sum of covariant terms is invariant.** If `G` acts on an index set `κ` and the terms
satisfy `h (g • k) = P_g h(k) P_g†`, then `∑_k h(k)` is invariant under the site action.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 862–863 and 1603–1613. -/
theorem isSiteInvariant_sum_of_covariant {κ : Type*} [Fintype κ] [MulAction G κ]
    (h : κ → Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ)
    (hcov : ∀ (g : G) k, h (g • k) =
      sitePermOp (MulAction.toPerm g) * h k * (sitePermOp (MulAction.toPerm g))ᴴ) :
    IsSiteInvariant G (∑ k, h k) :=
  isSiteInvariant_of_conj fun g ↦ by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ fun k ↦ (hcov g k).symm

/-- The sum `∑_g P_g H₀ P_g†` of the translates of one term is invariant under the site action. -/
theorem isSiteInvariant_sum_conj [Fintype G]
    (H₀ : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) :
    IsSiteInvariant G (∑ g : G, sitePermOp (MulAction.toPerm g) * H₀ *
      (sitePermOp (MulAction.toPerm g))ᴴ) :=
  isSiteInvariant_sum_of_covariant _ fun g k ↦ by
    simp only [smul_eq_mul, sitePermOp_toPerm_mul, conjTranspose_mul, Matrix.mul_assoc]

end ManyBody
