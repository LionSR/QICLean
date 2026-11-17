/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.RegionExpectation

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

The induced permutation of configurations carries the operators supported on a region to those
supported on the corresponding region (`reindex_siteConfigurationEquiv_mem_supportedOperators`)
and commutes with the region expectation (`reindex_siteConfigurationEquiv_regionExpectation`).
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

/-! ### Supported operators and the region expectation -/

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [∀ v, Fintype (X v)]
  [∀ v, Fintype (X' v)] [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (X' v)] in
/-- The relabelled configuration at a site `v` is the relabelled value at `e v`. -/
theorem siteConfigurationEquiv_symm_apply (e : V ≃ V') (f : ∀ v, X v ≃ X' (e v))
    (σ : Config X') (v : V) :
    (siteConfigurationEquiv e f).symm σ v = (f v).symm (σ (e v)) := by
  apply (f v).injective
  rw [Equiv.apply_symm_apply]
  conv_rhs => rw [← (siteConfigurationEquiv e f).apply_symm_apply σ]
  exact (Equiv.piCongr_apply_apply e f _ v).symm

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [∀ v, Fintype (X v)]
  [∀ v, Fintype (X' v)] [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (X' v)] in
private theorem forall_not_mem_iff (e : V ≃ V') (f : ∀ v, X v ≃ X' (e v)) {D : Finset V}
    {D' : Finset V'} (hD : ∀ v, v ∈ D ↔ e v ∈ D') (σ τ : Config X') :
    (∀ v ∉ D, (siteConfigurationEquiv e f).symm σ v = (siteConfigurationEquiv e f).symm τ v) ↔
      ∀ v' ∉ D', σ v' = τ v' := by
  rw [← e.forall_congr_right]
  refine forall_congr' fun v ↦ ?_
  rw [siteConfigurationEquiv_symm_apply, siteConfigurationEquiv_symm_apply,
    (f v).symm.injective.eq_iff, hD]

/-- Relabelling sites and basis labels carries the operators supported on `D` to the operators
supported on the corresponding region `D'`. -/
theorem reindex_siteConfigurationEquiv_mem_supportedOperators (e : V ≃ V')
    (f : ∀ v, X v ≃ X' (e v)) {D : Finset V} {D' : Finset V'} (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X D) :
    Matrix.reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) A ∈
      supportedOperators X' D' := by
  set φ := siteConfigurationEquiv e f
  refine ⟨fun σ τ ⟨v', hv', hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    refine hA.1 _ _ ?_
    by_contra hall
    push Not at hall
    exact hne ((forall_not_mem_iff e f hD σ τ).mp hall v' hv')
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.submatrix_apply]
    have hreg (σ σ' : Config X') (h : ∀ v' ∈ D', σ v' = σ' v') :
        ∀ v ∈ D, φ.symm σ v = φ.symm σ' v := fun v hv ↦ by
      rw [siteConfigurationEquiv_symm_apply, siteConfigurationEquiv_symm_apply,
        h (e v) ((hD v).mp hv)]
    exact hA.2 _ _ _ _ (hreg σ σ' h1) (hreg τ τ' h2) ((forall_not_mem_iff e f hD σ τ).mpr h3)
      ((forall_not_mem_iff e f hD σ' τ').mpr h4)

/-- The region expectation commutes with relabelling sites and basis labels. -/
theorem reindex_siteConfigurationEquiv_regionExpectation (e : V ≃ V')
    (f : ∀ v, X v ≃ X' (e v)) {D : Finset V} {D' : Finset V'} (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (A : Matrix (Config X) (Config X) ℂ) :
    Matrix.reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f)
        (regionExpectation D A) =
      regionExpectation D'
        (Matrix.reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) A) := by
  set φ := siteConfigurationEquiv e f
  set ρ := regionConfigurationEquiv D D' e hD f
  set ψ := complementConfigurationEquiv D D' e hD f
  have hcut (σ : Config X') :
      cutEquiv X D (φ.symm σ) = (ρ.prodCongr ψ).symm (cutEquiv X' D' σ) := rfl
  have hinv (a : RegionConfig X' D' × ComplConfig X' D') :
      φ.symm ((cutEquiv X' D').symm a) = (cutEquiv X D).symm ((ρ.prodCongr ψ).symm a) := by
    apply (cutEquiv X D).injective
    simpa only [Equiv.apply_symm_apply] using hcut ((cutEquiv X' D').symm a)
  have hcard : Fintype.card (ComplConfig X D) = Fintype.card (ComplConfig X' D') :=
    Fintype.card_congr ψ
  ext σ τ
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, regionExpectation_apply,
    regionExpectation_apply, hcard]
  congr 1
  refine if_congr (forall_not_mem_iff e f hD σ τ) ?_ rfl
  rw [← ψ.symm.sum_comp]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, hinv, hinv, hcut, hcut]
  rfl

end ManyBody
