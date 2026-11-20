/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SupportedMarginalTails
import QICLean.Entropy.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Relabel

/-!
# Regional states under bijections of tensor factors

A bijection of sites, together with bijections of the corresponding basis labels,
identifies the full configuration spaces and the configurations on any preserved
region. The regional state is covariant under this identification. Its entropy
is therefore invariant by `vonNeumannEntropy_submatrix_equiv`.

The statement includes pure site relabelling: for a dimension family `n'` on the
target sites, take the source family to be `fun v ↦ n' (e v)` and every basis
bijection to be the identity. No normalization, positive dimension, or geometric
assumption is required.

The configuration and vector abbreviations are reducible specializations of
`ManyBody.Sites.Relabel`, written in their original reduced form to preserve
`simp only` and `unfold` in downstream proofs. The covariance proofs delegate
to the generic results.
-/

namespace Entropy

variable {V V' : Type*} [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] {n : V → ℕ} {n' : V' → ℕ}

/-- The configuration bijection induced by site and basis-label bijections. -/
abbrev siteConfigurationEquiv (e : V ≃ V')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v))) : (∀ v, Fin (n v)) ≃ (∀ v, Fin (n' v)) :=
  e.piCongr f

/-- The induced configuration bijection on a preserved region. -/
abbrev regionConfigurationEquiv (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v))) :
    (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ≃
        (ManyBody.RegionConfig (fun v ↦ Fin (n' v)) D') :=
  (e.subtypeEquiv hD).piCongr (fun v ↦ f v.1)

export ManyBody (complementConfigurationEquiv)

/-- A vector expressed in the transported configuration basis. -/
noncomputable abbrev relabelVector (e : V ≃ V')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) : EuclideanSpace ℂ (∀ v, Fin (n' v)) :=
  WithLp.toLp 2 fun σ ↦ Ω ((siteConfigurationEquiv e f).symm σ)

/-- Expressing a vector in the transported configuration basis preserves its
Euclidean norm. -/
@[simp] theorem norm_relabelVector (e : V ≃ V')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ‖relabelVector e f Ω‖ = ‖Ω‖ :=
  ManyBody.norm_relabelVector (X := fun v ↦ Fin (n v)) (X' := fun v ↦ Fin (n' v))
    e f Ω

/-- Covariance of a regional pure-state matrix under site and basis-label
bijections. The vector need not be normalized. -/
theorem regionState_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ManyBody.regionState (relabelVector e f Ω) D' =
      (ManyBody.regionState Ω D).submatrix
        (regionConfigurationEquiv D D' e hD f).symm
        (regionConfigurationEquiv D D' e hD f).symm :=
  ManyBody.regionState_relabel (X := fun v ↦ Fin (n v)) (X' := fun v ↦ Fin (n' v))
    D D' e hD f Ω

/-- Regional entropy is invariant under site and basis-label bijections,
including for unnormalized vectors. -/
theorem regionEntropy_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ManyBody.regionEntropy (relabelVector e f Ω) D' = ManyBody.regionEntropy Ω D :=
  ManyBody.regionEntropy_relabel (X := fun v ↦ Fin (n v)) (X' := fun v ↦ Fin (n' v))
    D D' e hD f Ω

end Entropy
