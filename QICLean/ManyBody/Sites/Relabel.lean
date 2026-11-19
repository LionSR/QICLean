/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionState
import Mathlib.LinearAlgebra.Matrix.Permutation
import QICLean.Algebra.PermutationMatrixUnitary
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


section SitePermutation

/-! ### The site-permutation operator

For identical sites, a permutation `π` of the sites moves the content of every site `v` to the
site `π v`. Its operator is the permutation matrix of the configuration bijection
`siteConfigurationEquiv π⁻¹`, and conjugation by it is the reindexing along that bijection, so
that supported operators and the region expectation transform by the theorems above. -/

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [DecidableEq α]

omit [Fintype V] [DecidableEq V] [DecidableEq α] in
private theorem comp_symm_comp (σ : V → α) (π : Equiv.Perm V) : (σ ∘ ⇑π.symm) ∘ ⇑π = σ :=
  funext fun v ↦ congrArg σ (π.symm_apply_apply v)

omit [Fintype V] [DecidableEq V] [DecidableEq α] in
private theorem comp_comp_symm (σ : V → α) (π : Equiv.Perm V) : (σ ∘ ⇑π) ∘ ⇑π.symm = σ :=
  funext fun v ↦ congrArg σ (π.apply_symm_apply v)

/-- The operator moving the content of every site `v` to the site `π v`: it maps a vector `ψ`
to `σ ↦ ψ (σ ∘ π)`. -/
noncomputable def sitePermOp (π : Equiv.Perm V) :
    Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ :=
  Equiv.Perm.permMatrix ℂ (siteConfigurationEquiv (X := fun _ : V ↦ α) (X' := fun _ : V ↦ α)
    π⁻¹ fun _ ↦ Equiv.refl α)

omit [Fintype V] [DecidableEq V] [DecidableEq α] in
/-- Relabelling identical sites along `π` precomposes a configuration with `π⁻¹`. -/
theorem siteConfigurationEquiv_refl_apply (π : Equiv.Perm V) (σ : Config fun _ : V ↦ α) :
    siteConfigurationEquiv (X := fun _ : V ↦ α) (X' := fun _ : V ↦ α) π
      (fun _ ↦ Equiv.refl α) σ = σ ∘ π.symm := by
  have h : (siteConfigurationEquiv (X := fun _ : V ↦ α) (X' := fun _ : V ↦ α) π
      fun _ ↦ Equiv.refl α).symm (σ ∘ π.symm) = σ := by
    funext v
    rw [siteConfigurationEquiv, Equiv.piCongr_symm_apply]
    exact congrArg σ (π.symm_apply_apply v)
  exact ((Equiv.symm_apply_eq _).mp h).symm

omit [Fintype V] [DecidableEq V] [DecidableEq α] in
theorem siteConfigurationEquiv_inv_apply (π : Equiv.Perm V) (σ : Config fun _ : V ↦ α) :
    siteConfigurationEquiv (X := fun _ : V ↦ α) (X' := fun _ : V ↦ α) π⁻¹
      (fun _ ↦ Equiv.refl α) σ = σ ∘ π := by
  rw [siteConfigurationEquiv_refl_apply]
  rfl

omit [DecidableEq V] in
theorem sitePermOp_apply (π : Equiv.Perm V) (σ τ : Config fun _ : V ↦ α) :
    sitePermOp π σ τ = if τ = σ ∘ π then 1 else 0 := by
  simp only [sitePermOp, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, siteConfigurationEquiv_inv_apply]
  exact if_congr eq_comm rfl rfl

theorem sitePermOp_one : sitePermOp (V := V) (α := α) 1 = 1 := by
  ext σ τ
  simp [sitePermOp_apply, Matrix.one_apply, eq_comm]

variable [Fintype α]

theorem sitePermOp_mulVec (π : Equiv.Perm V) (ψ : (Config fun _ : V ↦ α) → ℂ) :
    sitePermOp π *ᵥ ψ = fun σ ↦ ψ (σ ∘ π) := by
  rw [sitePermOp, Matrix.permMatrix_mulVec]
  funext σ
  simp [siteConfigurationEquiv_inv_apply]

theorem sitePermOp_mul (π π' : Equiv.Perm V) :
    sitePermOp (α := α) π * sitePermOp π' = sitePermOp (π * π') := by
  ext σ τ
  simp only [Matrix.mul_apply, sitePermOp_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (σ ∘ π)]
  · simp only [ite_true]
    exact if_congr (by rw [Equiv.Perm.coe_mul, Function.comp_assoc]) rfl rfl
  · intro ρ _ hρ; simp [hρ]
  · simp

theorem sitePermOp_mem_unitary (π : Equiv.Perm V) :
    sitePermOp (α := α) π ∈ unitary (Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) :=
  Equiv.Perm.permMatrix_mem_unitaryGroup _

omit [Fintype α] in
theorem conjTranspose_sitePermOp (π : Equiv.Perm V) :
    (sitePermOp (α := α) π)ᴴ = sitePermOp π⁻¹ := by
  ext σ τ
  simp only [Matrix.conjTranspose_apply, sitePermOp_apply]
  by_cases h : σ = τ ∘ π
  · subst h; simp [Function.comp_assoc]
  · have h' : ¬τ = σ ∘ ⇑π⁻¹ := by rintro rfl; exact h (comp_symm_comp σ π).symm
    simp only [h, h', ↓reduceIte, star_zero]

/-- The action of `sitePermOp π` on a vector is the relabelling of its configurations along the
inverse permutation. -/
theorem sitePermOp_mulVec_eq_relabelVector (π : Equiv.Perm V)
    (ψ : EuclideanSpace ℂ (Config fun _ : V ↦ α)) :
    WithLp.toLp 2 (sitePermOp π *ᵥ ψ.ofLp) =
      relabelVector (X := fun _ : V ↦ α) (X' := fun _ : V ↦ α) π (fun _ ↦ Equiv.refl α) ψ := by
  simp only [relabelVector, sitePermOp_mulVec]
  congr 1

/-- Conjugation by the site-permutation operator is the reindexing along the configuration
bijection `siteConfigurationEquiv π`. -/
theorem sitePermOp_mul_mul_conjTranspose (π : Equiv.Perm V)
    (A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) :
    sitePermOp π * A * (sitePermOp π)ᴴ =
      Matrix.reindex (siteConfigurationEquiv π fun _ ↦ Equiv.refl α)
        (siteConfigurationEquiv π fun _ ↦ Equiv.refl α) A := by
  ext σ τ
  rw [conjTranspose_sitePermOp, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Matrix.mul_apply, sitePermOp_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hinv (ρ : Config fun _ : V ↦ α) : (siteConfigurationEquiv (X := fun _ : V ↦ α)
      (X' := fun _ : V ↦ α) π fun _ ↦ Equiv.refl α).symm ρ = ρ ∘ π := by
    rw [Equiv.symm_apply_eq, siteConfigurationEquiv_refl_apply]
    exact (comp_comp_symm ρ π).symm
  rw [hinv, hinv, Finset.sum_eq_single (τ ∘ π)]
  · simp [Function.comp_assoc]
  · intro ρ _ hρ
    have h' : ¬τ = ρ ∘ ⇑π⁻¹ := by rintro rfl; exact hρ (comp_symm_comp ρ π).symm
    simp only [h', ↓reduceIte]
  · simp

/-- A supported operator conjugated by the site-permutation operator is supported on the
permuted region. -/
theorem sitePermOp_mul_mul_conjTranspose_mem_supportedOperators (π : Equiv.Perm V)
    {D : Finset V} {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) D) :
    sitePermOp π * A * (sitePermOp π)ᴴ ∈ supportedOperators (fun _ : V ↦ α) (D.image π) := by
  rw [sitePermOp_mul_mul_conjTranspose]
  exact reindex_siteConfigurationEquiv_mem_supportedOperators π _
    (fun v ↦ by simp [π.injective.eq_iff]) hA

/-- The region expectation commutes with conjugation by the site-permutation operator. -/
theorem sitePermOp_mul_mul_conjTranspose_regionExpectation (π : Equiv.Perm V) (D : Finset V)
    (A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) :
    sitePermOp π * regionExpectation D A * (sitePermOp π)ᴴ =
      regionExpectation (D.image π) (sitePermOp π * A * (sitePermOp π)ᴴ) := by
  rw [sitePermOp_mul_mul_conjTranspose, sitePermOp_mul_mul_conjTranspose]
  exact reindex_siteConfigurationEquiv_regionExpectation π _
    (fun v ↦ by simp [π.injective.eq_iff]) A

end SitePermutation

end ManyBody
