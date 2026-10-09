/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift

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
-/

namespace Entropy

variable {V V' : Type*} [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] {n : V → ℕ} {n' : V' → ℕ}

/-- The configuration bijection induced by site and basis-label bijections. -/
def siteConfigurationEquiv (e : V ≃ V')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v))) : SiteConfig n ≃ SiteConfig n' :=
  e.piCongr f

/-- The induced configuration bijection on a preserved region. -/
def regionConfigurationEquiv (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v))) :
    RegionConfig n D ≃ RegionConfig n' D' :=
  (e.subtypeEquiv hD).piCongr (fun v ↦ f v.1)

/-- The induced configuration bijection on the complementary region. -/
def complementConfigurationEquiv (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v))) :
    ((v : {v // v ∉ D}) → Fin (n v)) ≃
      ((v : {v // v ∉ D'}) → Fin (n' v)) :=
  (e.subtypeEquiv (fun v ↦ not_congr (hD v))).piCongr (fun v ↦ f v.1)

/-- A vector expressed in the transported configuration basis. -/
noncomputable def relabelVector (e : V ≃ V')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) : EuclideanSpace ℂ (SiteConfig n') :=
  WithLp.toLp 2 fun σ ↦ Ω ((siteConfigurationEquiv e f).symm σ)

/-- Covariance of a regional pure-state matrix under site and basis-label
bijections. The vector need not be normalized. -/
theorem regionState_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    regionState D' (relabelVector e f Ω) =
      (regionState D Ω).submatrix
        (regionConfigurationEquiv D D' e hD f).symm
        (regionConfigurationEquiv D D' e hD f).symm := by
  refine Eq.trans ?_ (Matrix.partialTraceRight_submatrix_prod_equiv
    (regionConfigurationEquiv D D' e hD f)
    (complementConfigurationEquiv D D' e hD f)
    (Matrix.vecMulVec (WithLp.ofLp (cutVector D Ω))
      (star (WithLp.ofLp (cutVector D Ω)))))
  have hcut (σ : SiteConfig n') :
      cutEquiv n D ((siteConfigurationEquiv e f).symm σ) =
        ((regionConfigurationEquiv D D' e hD f).prodCongr
          (complementConfigurationEquiv D D' e hD f)).symm (cutEquiv n' D' σ) := by
    rfl
  have hinv (a : RegionConfig n' D' × ((v : {v // v ∉ D'}) → Fin (n' v))) :
      (siteConfigurationEquiv e f).symm ((cutEquiv n' D').symm a) =
        (cutEquiv n D).symm
          (((regionConfigurationEquiv D D' e hD f).prodCongr
            (complementConfigurationEquiv D D' e hD f)).symm a) := by
    apply (cutEquiv n D).injective
    simpa only [Equiv.apply_symm_apply] using hcut ((cutEquiv n' D').symm a)
  refine congrArg Matrix.partialTraceRight ?_
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.submatrix_apply, Pi.star_apply,
    relabelVector, WithLp.ofLp_toLp, hinv]

/-- Regional entropy is invariant under site and basis-label bijections,
including for unnormalized vectors. -/
theorem regionEntropy_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    regionEntropy D' (relabelVector e f Ω) = regionEntropy D Ω := by
  simp only [regionEntropy, regionState_relabel D D' e hD f Ω]
  exact vonNeumannEntropy_submatrix_equiv
    (regionConfigurationEquiv D D' e hD f).symm (regionState D Ω)
    (regionState_isHermitian D Ω)

end Entropy
