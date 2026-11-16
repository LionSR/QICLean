/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionState

/-!
# Regional states under bijections of tensor factors

A bijection of sites, together with bijections of the corresponding basis labels,
identifies the full configuration spaces and the configurations on any preserved
region. The regional state is covariant under this identification. Its entropy
is therefore invariant by `vonNeumannEntropy_submatrix_equiv`.

The statement includes pure site relabelling: for a basis family `X'` on the
target sites, take the source family to be `fun v ↦ X' (e v)` and every basis
bijection to be the identity. No normalization, positive dimension, or geometric
assumption is required.
-/

namespace ManyBody

variable {V V' : Type*} [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] {X : V → Type*} {X' : V' → Type*}
  [∀ v, Fintype (X v)] [∀ v, Fintype (X' v)]

/-- The configuration bijection induced by site and basis-label bijections. -/
def siteConfigurationEquiv (e : V ≃ V')
    (f : ∀ v, X v ≃ X' (e v)) : Config X ≃ Config X' :=
  e.piCongr f

/-- The induced configuration bijection on a preserved region. -/
def regionConfigurationEquiv (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, X v ≃ X' (e v)) :
    RegionConfig X D ≃ RegionConfig X' D' :=
  (e.subtypeEquiv hD).piCongr (fun v ↦ f v.1)

/-- The induced configuration bijection on the complementary region. -/
def complementConfigurationEquiv (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, X v ≃ X' (e v)) :
    ((v : {v // v ∉ D}) → X v) ≃
      ((v : {v // v ∉ D'}) → X' v) :=
  (e.subtypeEquiv (fun v ↦ not_congr (hD v))).piCongr (fun v ↦ f v.1)

/-- A vector expressed in the transported configuration basis. -/
noncomputable def relabelVector (e : V ≃ V')
    (f : ∀ v, X v ≃ X' (e v))
    (Ω : EuclideanSpace ℂ (Config X)) : EuclideanSpace ℂ (Config X') :=
  WithLp.toLp 2 fun σ ↦ Ω ((siteConfigurationEquiv e f).symm σ)

/-- Expressing a vector in the transported configuration basis preserves its
Euclidean norm. -/
@[simp] theorem norm_relabelVector (e : V ≃ V')
    (f : ∀ v, X v ≃ X' (e v))
    (Ω : EuclideanSpace ℂ (Config X)) :
    ‖relabelVector e f Ω‖ = ‖Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (siteConfigurationEquiv e f)).norm_map Ω

/-- Covariance of a regional pure-state matrix under site and basis-label
bijections. The vector need not be normalized. -/
theorem regionState_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, X v ≃ X' (e v))
    (Ω : EuclideanSpace ℂ (Config X)) :
    regionState D' (relabelVector e f Ω) =
      (regionState D Ω).submatrix
        (regionConfigurationEquiv D D' e hD f).symm
        (regionConfigurationEquiv D D' e hD f).symm := by
  refine Eq.trans ?_ (Matrix.partialTraceRight_submatrix_prod_equiv
    (regionConfigurationEquiv D D' e hD f)
    (complementConfigurationEquiv D D' e hD f)
    (Matrix.vecMulVec (WithLp.ofLp (cutVector D Ω))
      (star (WithLp.ofLp (cutVector D Ω)))))
  have hcut (σ : Config X') :
      cutEquiv X D ((siteConfigurationEquiv e f).symm σ) =
        ((regionConfigurationEquiv D D' e hD f).prodCongr
          (complementConfigurationEquiv D D' e hD f)).symm (cutEquiv X' D' σ) := by
    rfl
  have hinv (a : RegionConfig X' D' × ((v : {v // v ∉ D'}) → X' v)) :
      (siteConfigurationEquiv e f).symm ((cutEquiv X' D').symm a) =
        (cutEquiv X D).symm
          (((regionConfigurationEquiv D D' e hD f).prodCongr
            (complementConfigurationEquiv D D' e hD f)).symm a) := by
    apply (cutEquiv X D).injective
    simpa only [Equiv.apply_symm_apply] using hcut ((cutEquiv X' D').symm a)
  refine congrArg Matrix.partialTraceRight ?_
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.submatrix_apply, Pi.star_apply,
    relabelVector, WithLp.ofLp_toLp, hinv]

variable [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (X' v)]

/-- Regional entropy is invariant under site and basis-label bijections,
including for unnormalized vectors. -/
theorem regionEntropy_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, X v ≃ X' (e v))
    (Ω : EuclideanSpace ℂ (Config X)) :
    regionEntropy D' (relabelVector e f Ω) = regionEntropy D Ω := by
  simp only [regionEntropy, regionState_relabel D D' e hD f Ω]
  exact vonNeumannEntropy_submatrix_equiv
    (regionConfigurationEquiv D D' e hD f).symm (regionState D Ω)
    (regionState_isHermitian D Ω)

end ManyBody
