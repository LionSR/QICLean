/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift

/-!
# Regional states under a relabelling of sites

Let `e : V ≃ V'` be a bijection of finite site sets, with the local dimension of a site
`v ∈ V` equal to that of its image `e v`. Pulling coefficients back along `e` identifies a
vector of `⊗_{v ∈ V} ℂ^{n_{e v}}` with a vector of `⊗_{v' ∈ V'} ℂ^{n_{v'}}`. When `e` carries
a region `A ⊆ V` onto a region `A' ⊆ V'`, the identification restricts to the configurations
of `A` and of its complement. Partial trace is covariant under this identification, so the
regional state on `A'` of the relabelled vector is the regional state on `A` conjugated by
the induced relabelling of regional configurations, and the regional entropies agree. No
normalization of the vector is required.

## Main results

* `Entropy.relabelSites`: a vector rewritten after relabelling its sites.
* `Entropy.norm_relabelSites`: relabelling preserves the Euclidean norm.
* `Entropy.regionState_relabelSites`: covariance of the regional state.
* `Entropy.regionEntropy_relabelSites`: invariance of the regional entropy.
-/

open Complex Matrix

namespace Entropy

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {n : V' → ℕ}

/-- Configuration transport along a site bijection `e : V ≃ V'`, where the dimension of
`v ∈ V` is that of `e v`. -/
abbrev siteConfigRelabel (n : V' → ℕ) (e : V ≃ V') :
    SiteConfig (fun v ↦ n (e v)) ≃ SiteConfig n :=
  Equiv.piCongrLeft (fun v' ↦ Fin (n v')) e

/-- Configuration transport of a region `A` that a site bijection carries onto `A'`. -/
abbrev regionConfigRelabel (n : V' → ℕ) (e : V ≃ V') {A : Finset V} {A' : Finset V'}
    (hA : ∀ v, v ∈ A ↔ e v ∈ A') :
    RegionConfig (fun v ↦ n (e v)) A ≃ RegionConfig n A' :=
  Equiv.piCongrLeft (fun v' : {v' // v' ∈ A'} ↦ Fin (n v'.1)) (e.subtypeEquiv hA)

/-- Configuration transport of the complement of a region that a site bijection carries
onto `A'`. -/
abbrev complConfigRelabel (n : V' → ℕ) (e : V ≃ V') {A : Finset V} {A' : Finset V'}
    (hA : ∀ v, v ∈ A ↔ e v ∈ A') :
    ((v : {v // v ∉ A}) → Fin (n (e v))) ≃ ((v' : {v' // v' ∉ A'}) → Fin (n v')) :=
  Equiv.piCongrLeft (fun v' : {v' // v' ∉ A'} ↦ Fin (n v'.1))
    (e.subtypeEquiv fun v ↦ not_congr (hA v))

/-- The vector `Ω` written after relabelling its sites along `e : V ≃ V'`. -/
noncomputable def relabelSites (e : V ≃ V') (Ω : EuclideanSpace ℂ (SiteConfig fun v ↦ n (e v))) :
    EuclideanSpace ℂ (SiteConfig n) :=
  WithLp.toLp 2 fun σ ↦ Ω ((siteConfigRelabel n e).symm σ)

/-- Relabelling sites preserves the Euclidean norm. -/
@[simp] theorem norm_relabelSites (e : V ≃ V')
    (Ω : EuclideanSpace ℂ (SiteConfig fun v ↦ n (e v))) :
    ‖relabelSites e Ω‖ = ‖Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (siteConfigRelabel n e)).norm_map Ω

omit [Fintype V] [Fintype V'] in
/-- Splitting a relabelled configuration along `A'` is relabelling its two parts. -/
theorem siteConfigRelabel_symm_cutEquiv_symm (e : V ≃ V') {A : Finset V} {A' : Finset V'}
    (hA : ∀ v, v ∈ A ↔ e v ∈ A')
    (x : RegionConfig n A' × ((v' : {v' // v' ∉ A'}) → Fin (n v'))) :
    (siteConfigRelabel n e).symm ((cutEquiv n A').symm x) =
      (cutEquiv (fun v ↦ n (e v)) A).symm
        (((regionConfigRelabel n e hA).prodCongr (complConfigRelabel n e hA)).symm x) := by
  funext v
  by_cases hv : v ∈ A
  · rw [cutEquiv_symm_apply_mem _ _ hv]
    simp only [Equiv.piCongrLeft_symm_apply, cutEquiv_symm_apply_mem _ _ ((hA v).mp hv)]
    rfl
  · rw [cutEquiv_symm_apply_not_mem _ _ hv]
    simp only [Equiv.piCongrLeft_symm_apply,
      cutEquiv_symm_apply_not_mem _ _ (fun h ↦ hv ((hA v).mpr h))]
    rfl

/-- The regional state is covariant under a site bijection carrying `A` onto `A'`: the
regional state on `A'` of the relabelled vector is the regional state on `A` with its
configurations relabelled. -/
theorem regionState_relabelSites (e : V ≃ V') {A : Finset V} {A' : Finset V'}
    (hA : ∀ v, v ∈ A ↔ e v ∈ A') (Ω : EuclideanSpace ℂ (SiteConfig fun v ↦ n (e v))) :
    regionState A' (relabelSites e Ω) =
      (regionState A Ω).submatrix (regionConfigRelabel n e hA).symm
        (regionConfigRelabel n e hA).symm := by
  refine Eq.trans ?_ (partialTraceRight_submatrix_prod_equiv (regionConfigRelabel n e hA)
    (complConfigRelabel n e hA) _)
  unfold regionState
  congr 1
  ext x y
  simp only [relabelSites, submatrix_apply, vecMulVec_apply, Pi.star_apply]
  rw [siteConfigRelabel_symm_cutEquiv_symm e hA x, siteConfigRelabel_symm_cutEquiv_symm e hA y]

/-- The regional entropy is invariant under a site bijection carrying `A` onto `A'`. -/
theorem regionEntropy_relabelSites (e : V ≃ V') {A : Finset V} {A' : Finset V'}
    (hA : ∀ v, v ∈ A ↔ e v ∈ A') (Ω : EuclideanSpace ℂ (SiteConfig fun v ↦ n (e v))) :
    regionEntropy A' (relabelSites e Ω) = regionEntropy A Ω := by
  simpa only [regionEntropy, regionState_relabelSites e hA Ω] using
    vonNeumannEntropy_submatrix_equiv (regionConfigRelabel n e hA).symm
      (regionState A Ω) (regionState_isHermitian A Ω)

end Entropy
