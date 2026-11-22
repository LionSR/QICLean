/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Relabel
import QICLean.ManyBody.Sites.RegionUnion
import QICLean.Analysis.Norm.L2OpNormReindex

/-!
# Placement along an injection of sites

Let `w : W ↪ V` be an injection of a finite set of sites `W` into the sites `V` of a system `X`,
and give the site `u` of `W` the basis `X (w u)`. A matrix `K` on the configurations of `W` acts
on the whole system as `K ⊗ 1`, with `K` acting on the sites `w u` and the identity on the sites
outside the image of `w`. This operator, `ManyBody.placeAlong w K`, is the placement of `K` on
the image region `w(W)`, after the sites of `W` are identified with those of the image
(`ManyBody.windowEquiv`, `ManyBody.windowConfigEquiv`). It is therefore a unital
`*`-homomorphism with the norm, order and support properties of `ManyBody.place`.

The injection need not be a bijection: the windows of consecutive sites of a ring or of an open
chain, a finite set of sites inside a larger one, and an injection of the sites of a smaller
system are the main cases. Placing along the inclusion of a region is placing on that region
(`ManyBody.placeAlong_subtype`), placing along a bijection of the sites is relabelling the
configurations (`ManyBody.placeAlong_equiv`), and placements along composable injections compose
(`ManyBody.placeAlong_placeAlong`). An operator supported on a region `S` of `W` is placed onto
an operator supported on the image of `S` (`ManyBody.placeAlong_mem_supportedOperators_map`). On
identical sites, conjugation by the permutation operator of a permutation `π` of `V` moves the
placement along `w` to the placement along `π ∘ w`
(`ManyBody.sitePermOp_mul_placeAlong_mul_conjTranspose`); for the windows of a ring and the
rotation of the ring, this is the translation of one window to the next.

## Main definitions

* `ManyBody.windowEquiv` — the sites `W` identified with their image under an injection.
* `ManyBody.windowConfigEquiv` — the configurations of `W` identified with those of the image.
* `ManyBody.placeAlong` — the placement `K ↦ K ⊗ 1` along an injection of sites.
* `ManyBody.placeAlongHom` — the placement along an injection as a `*`-homomorphism.
* `ManyBody.placeAt` — a matrix at one site, placed along the inclusion of the site.

## Main results

* `ManyBody.placeAlong_apply`, `ManyBody.placeAlong_mulVec_apply_of` — entries and action on a
  vector.
* `ManyBody.placeAlong_mul`, `ManyBody.placeAlong_one`, `ManyBody.placeAlong_conjTranspose`, the
  linear lemmas, `ManyBody.placeAlong_mem_unitaryGroup` and `ManyBody.trace_placeAlong`.
* `ManyBody.placeAlong_mem_supportedOperators`,
  `ManyBody.placeAlong_mem_supportedOperators_map`.
* `ManyBody.norm_placeAlong_le`, `ManyBody.norm_placeAlong`, `ManyBody.posSemidef_placeAlong`,
  `ManyBody.posSemidef_placeAlong_iff`, `ManyBody.placeAlong_le_placeAlong_iff`,
  `ManyBody.placeAlong_injective`.
* `ManyBody.placeAlong_subtype`, `ManyBody.placeAlong_equiv`, `ManyBody.placeAlong_refl`,
  `ManyBody.placeAlong_placeAlong`, `ManyBody.placeAlong_prodOp`.
* `ManyBody.sitePermOp_mul_placeAlong_mul_conjTranspose`.
* `ManyBody.place_siteEquiv_eq_placeAt` — a matrix on the region `{v}`, read through the basis of
  `v`, is the matrix at `v`; `ManyBody.placeAt_eq_prodOp`, `ManyBody.placeAt_mulVec_apply`.

These replace TNLean's placements `QuantumCircuit.embedOp` (`Circuit/SiteEmbedding`) and
`MPOTensor.embedLocalOperator` (`MPS/MPDO/CommutingForm`) at TNLean commit `414a18fb88`: the
first is the placement along an injection `κ ↪ ι`, and the second is the placement along the
window of `L` consecutive sites of a ring, `ManyBody.ringWindow`. The lemmas on one site
restate those on `siteOp` of `TNLean/Circuit/SiteOperators.lean` at the same commit
(Apache-2.0), with `ManyBody.placeAt` in place of `siteOp` and any finite basis at each site in
place of one common dimension.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ManyBody

/-! ### The image of an injection -/

section Window

variable {V W : Type*} [Fintype W] {X : V → Type*}

/-- The sites `W` identified with their image under an injection `w : W ↪ V`. -/
noncomputable def windowEquiv (w : W ↪ V) : W ≃ ↥(Finset.univ.map w) :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans (Finset.univ.equivMap w)

@[simp]
theorem coe_windowEquiv (w : W ↪ V) (u : W) : (windowEquiv w u : V) = w u :=
  rfl

/-- The configurations of the sites `W`, the site `u` carrying the basis `X (w u)`, are the
configurations of the image region `w(W)`. -/
noncomputable def windowConfigEquiv (w : W ↪ V) :
    Config (fun u ↦ X (w u)) ≃ RegionConfig X (Finset.univ.map w) :=
  Equiv.piCongrLeft (fun v : {v // v ∈ Finset.univ.map w} ↦ X v) (windowEquiv w)

/-- A configuration of the image, read at the sites of `W`. -/
@[simp]
theorem windowConfigEquiv_symm_apply (w : W ↪ V) (a : RegionConfig X (Finset.univ.map w))
    (u : W) : (windowConfigEquiv w).symm a u = a (windowEquiv w u) :=
  rfl

/-- A configuration of `W`, read at the image of a site. -/
@[simp]
theorem windowConfigEquiv_apply_windowEquiv (w : W ↪ V) (a : Config fun u ↦ X (w u)) (u : W) :
    windowConfigEquiv w a (windowEquiv w u) = a u :=
  Equiv.piCongrLeft_apply_apply (fun v : {v // v ∈ Finset.univ.map w} ↦ X v) (windowEquiv w) a u

end Window

/-! ### The placement -/

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, DecidableEq (X v)]
  {W : Type*} [Fintype W] (w : W ↪ V)

/-- **Placement along an injection of sites.** For an injection `w : W ↪ V` and a matrix `K` on
the configurations of `W`, the site `u` carrying the basis `X (w u)`, the operator `K ⊗ 1` on the
whole system: `K` acts on the sites `w u` and the identity on the sites outside the image of
`w`. It is the placement of `K` on the image region `w(W)`. -/
noncomputable def placeAlong
    (K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) :
    Matrix (Config X) (Config X) ℂ :=
  place (Finset.univ.map w) (reindex (windowConfigEquiv w) (windowConfigEquiv w) K)

/-- Entries of a matrix placed along an injection: the entry of `K` at the restrictions of `σ`
and `τ` to the image when `σ` and `τ` agree outside the image, and zero otherwise. -/
theorem placeAlong_apply (K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ)
    (σ τ : Config X) :
    placeAlong w K σ τ =
      if ∀ v, (∀ u, w u ≠ v) → σ v = τ v then K (fun u ↦ σ (w u)) (fun u ↦ τ (w u)) else 0 := by
  rw [placeAlong, place_apply, reindex_apply, submatrix_apply]
  refine if_congr ?_ rfl rfl
  simp

/-! ### Algebraic properties -/

section Algebra

variable (K K' : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ)

@[simp]
theorem placeAlong_zero :
    placeAlong w (0 : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) = 0 := by
  simp [placeAlong]

theorem placeAlong_add : placeAlong w (K + K') = placeAlong w K + placeAlong w K' := by
  rw [placeAlong, placeAlong, placeAlong, ← place_add]
  rfl

theorem placeAlong_smul (c : ℂ) : placeAlong w (c • K) = c • placeAlong w K := by
  rw [placeAlong, placeAlong, ← place_smul]
  rfl

theorem placeAlong_neg : placeAlong w (-K) = -placeAlong w K := by
  rw [← neg_one_smul ℂ K, placeAlong_smul, neg_one_smul]

theorem placeAlong_sub : placeAlong w (K - K') = placeAlong w K - placeAlong w K' := by
  rw [sub_eq_add_neg, placeAlong_add, placeAlong_neg, sub_eq_add_neg]

theorem placeAlong_sum {ι : Type*} (s : Finset ι)
    (K : ι → Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) :
    placeAlong w (∑ i ∈ s, K i) = ∑ i ∈ s, placeAlong w (K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, placeAlong_add, ih]

theorem placeAlong_conjTranspose : placeAlong w Kᴴ = (placeAlong w K)ᴴ := by
  rw [placeAlong, placeAlong, ← conjTranspose_reindex, place_conjTranspose]

variable {K} in
/-- A Hermitian matrix placed along an injection is Hermitian. -/
theorem isHermitian_placeAlong (hK : K.IsHermitian) : (placeAlong w K).IsHermitian :=
  hK.apply_of_map_conjTranspose (placeAlong_conjTranspose w)

/-- The placement of the identity is the identity, for every decidable equality of the
configurations of `W` and of the system. -/
@[simp]
theorem placeAlong_one [DecidableEq (Config fun u ↦ X (w u))] [DecidableEq (Config X)] :
    placeAlong w (1 : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) = 1 := by
  obtain rfl : ‹DecidableEq (Config X)› = Fintype.decidablePiFintype := Subsingleton.elim _ _
  classical
  rw [placeAlong, reindex_apply, submatrix_one_equiv, place_one]

variable [∀ v, Fintype (X v)]

theorem placeAlong_mul [Fintype (Config fun u ↦ X (w u))] :
    placeAlong w (K * K') = placeAlong w K * placeAlong w K' := by
  classical
  rw [placeAlong, placeAlong, placeAlong, ← place_mul, reindex_apply, reindex_apply,
    reindex_apply, submatrix_mul_equiv]

theorem placeAlong_pow [Fintype (Config fun u ↦ X (w u))] [DecidableEq (Config fun u ↦ X (w u))]
    (k : ℕ) : placeAlong w (K ^ k) = placeAlong w K ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, placeAlong_one]
  | succ k ih => rw [pow_succ, pow_succ, placeAlong_mul, ih]

/-- The placement of a unitary matrix along an injection is unitary. -/
theorem placeAlong_mem_unitaryGroup [Fintype (Config fun u ↦ X (w u))]
    [DecidableEq (Config fun u ↦ X (w u))] {K : Matrix (Config fun u ↦ X (w u))
      (Config fun u ↦ X (w u)) ℂ} (hK : K ∈ unitaryGroup _ ℂ) :
    placeAlong w K ∈ unitaryGroup (Config X) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ← placeAlong_conjTranspose,
    ← placeAlong_mul, ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hK, placeAlong_one]

/-- The placement along an injection as a unital `*`-homomorphism from the matrix algebra of the
sites `W` to the matrix algebra of the system. The unit of each algebra depends on a decidable
equality of its configurations; both decidable equalities are instance arguments, so that the
homomorphism exists for every choice of them. -/
noncomputable def placeAlongHom [DecidableEq W] [DecidableEq (Config fun u ↦ X (w u))]
    [DecidableEq (Config X)] :
    Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ →⋆ₐ[ℂ]
      Matrix (Config X) (Config X) ℂ where
  toFun := placeAlong w
  map_one' := placeAlong_one w
  map_mul' K K' := by classical exact placeAlong_mul w K K'
  map_zero' := placeAlong_zero w
  map_add' K K' := placeAlong_add w K K'
  commutes' c := by
    classical
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, placeAlong_smul,
      placeAlong_one]
  map_star' K := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, placeAlong_conjTranspose]

@[simp]
theorem placeAlongHom_apply [DecidableEq W] [DecidableEq (Config fun u ↦ X (w u))]
    [DecidableEq (Config X)] :
    placeAlongHom w K = placeAlong w K :=
  rfl

/-- The trace of a matrix placed along an injection is its trace times the number of
configurations outside the image. -/
theorem trace_placeAlong [Fintype (Config fun u ↦ X (w u))] :
    (placeAlong w K).trace = Fintype.card (ComplConfig X (Finset.univ.map w)) * K.trace := by
  classical
  rw [placeAlong, trace_place, reindex_apply, trace_submatrix_equiv]

/-- **The action on a vector.** Let `g a` be the configuration equal to `a u` at the site `w u`
and to `σ` outside the image of `w`. A matrix placed along `w` maps a vector `ψ` to the vector
whose component at `σ` is `∑ₐ K (σ ∘ w, a) ψ (g a)`. -/
theorem placeAlong_mulVec_apply_of [Fintype (Config fun u ↦ X (w u))] (ψ : Config X → ℂ)
    (σ : Config X) (g : (Config fun u ↦ X (w u)) → Config X) (hg : ∀ a u, g a (w u) = a u)
    (hg' : ∀ a v, (∀ u, w u ≠ v) → g a v = σ v) :
    (placeAlong w K *ᵥ ψ) σ = ∑ a, K (fun u ↦ σ (w u)) a * ψ (g a) := by
  classical
  rw [placeAlong, place_mulVec_apply, ← (windowConfigEquiv w).sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  congr 2
  funext v
  by_cases hv : v ∈ Finset.univ.map w
  · obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hv
    rw [cutEquiv_symm_apply_mem _ _ hv, hg]
    exact windowConfigEquiv_apply_windowEquiv w a u
  · rw [cutEquiv_symm_apply_not_mem _ _ hv, hg' a v fun u hu ↦ hv (hu ▸ Finset.mem_map_of_mem _
      (Finset.mem_univ u))]
    rfl

omit [∀ v, Fintype (X v)] in
/-- A diagonal matrix placed along an injection is the diagonal matrix whose entry at `σ` is the
entry at the restriction `σ ∘ w`. -/
theorem placeAlong_diagonal (f : (Config fun u ↦ X (w u)) → ℂ) :
    placeAlong w (diagonal f) = diagonal fun σ ↦ f fun u ↦ σ (w u) := by
  ext σ τ
  rw [placeAlong_apply, diagonal_apply, diagonal_apply]
  by_cases h : σ = τ
  · subst h
    simp
  · rw [ite_eq_right h]
    split_ifs with h1 h2
    · refine absurd (funext fun v ↦ ?_) h
      by_cases hv : ∃ u, w u = v
      · obtain ⟨u, rfl⟩ := hv
        exact congrFun h2 u
      · exact h1 v (not_exists.mp hv)
    · rfl
    · rfl

/-- Placement along an injection commutes with the exponential. -/
theorem placeAlong_exp [DecidableEq W] [DecidableEq (Config fun u ↦ X (w u))] :
    placeAlong w (NormedSpace.exp K) = NormedSpace.exp (placeAlong w K) := by
  let _ : NormedAlgebra ℚ (Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (placeAlongHom w)
    (placeAlongHom w).toLinearMap.continuous_of_finiteDimensional K

end Algebra

/-! ### Supports -/

section Support

variable [∀ v, Fintype (X v)]

/-- A matrix placed along an injection is supported on the image. -/
theorem placeAlong_mem_supportedOperators
    (K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) :
    placeAlong w K ∈ supportedOperators X (Finset.univ.map w) :=
  place_mem_supportedOperators _

/-- **Image support.** An operator on the sites `W` supported on `S` is placed along `w` onto an
operator supported on the image of `S`. -/
theorem placeAlong_mem_supportedOperators_map [DecidableEq W] {S : Finset W}
    {K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ}
    (hK : K ∈ supportedOperators (fun u ↦ X (w u)) S) :
    placeAlong w K ∈ supportedOperators X (S.map w) := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [placeAlong_apply]
    split_ifs with h
    · by_cases hr : ∃ u, w u = v
      · obtain ⟨u, rfl⟩ := hr
        exact hK.1 _ _ ⟨u, fun hu ↦ hv (Finset.mem_map_of_mem w hu), hne⟩
      · exact absurd (h v (not_exists.mp hr)) hne
    · rfl
  · have hout (v : V) (hv : ∀ u, w u ≠ v) : v ∉ S.map w := fun h ↦ by
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp h
      exact hv u rfl
    rw [placeAlong_apply, placeAlong_apply, ite_eq_left fun v hv ↦ h3 v (hout v hv),
      ite_eq_left fun v hv ↦ h4 v (hout v hv)]
    exact hK.2 _ _ _ _ (fun u hu ↦ h1 _ (Finset.mem_map_of_mem w hu))
      (fun u hu ↦ h2 _ (Finset.mem_map_of_mem w hu))
      (fun u hu ↦ h3 _ ((Finset.mem_map' w).not.mpr hu))
      (fun u hu ↦ h4 _ ((Finset.mem_map' w).not.mpr hu))

/-- Every operator supported on the image of an injection is placed along it. -/
theorem exists_eq_placeAlong_of_mem_supportedOperators {A : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X (Finset.univ.map w)) :
    ∃ K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ, A = placeAlong w K := by
  obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators hA
  refine ⟨reindex (windowConfigEquiv w).symm (windowConfigEquiv w).symm K, ?_⟩
  rw [placeAlong, ← reindex_symm, Equiv.apply_symm_apply]

/-- An operator is supported on the image of an injection exactly when it is placed along it. -/
theorem mem_supportedOperators_iff_exists_eq_placeAlong {A : Matrix (Config X) (Config X) ℂ} :
    A ∈ supportedOperators X (Finset.univ.map w) ↔
      ∃ K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ, A = placeAlong w K :=
  ⟨exists_eq_placeAlong_of_mem_supportedOperators w, by
    rintro ⟨K, rfl⟩
    exact placeAlong_mem_supportedOperators w K⟩

/-- Matrices placed along injections with disjoint images commute. -/
theorem commute_placeAlong_of_disjoint {W' : Type*} [Fintype W'] {w' : W' ↪ V}
    (h : Disjoint (Finset.univ.map w) (Finset.univ.map w'))
    (K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ)
    (K' : Matrix (Config fun u ↦ X (w' u)) (Config fun u ↦ X (w' u)) ℂ) :
    Commute (placeAlong w K) (placeAlong w' K') :=
  commute_of_mem_supportedOperators_of_disjoint (placeAlong_mem_supportedOperators w K)
    (placeAlong_mem_supportedOperators w' K') h

end Support

/-! ### Norm, order and injectivity -/

section Order

variable [∀ v, Fintype (X v)]

variable [DecidableEq W] in
theorem norm_placeAlong_le (K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) :
    ‖placeAlong w K‖ ≤ ‖K‖ := by
  classical
  exact (norm_place_le _).trans (Matrix.l2_opNorm_reindex_equiv _ K).le

omit [∀ v, Fintype (X v)] in
/-- A positive semidefinite matrix placed along an injection is positive semidefinite. -/
theorem posSemidef_placeAlong [∀ v, Finite (X v)]
    {K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ} (hK : K.PosSemidef) :
    (placeAlong w K).PosSemidef :=
  posSemidef_place (hK.submatrix _)

omit [∀ v, Fintype (X v)] in
theorem placeAlong_le_placeAlong [∀ v, Finite (X v)]
    {K K' : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ} (h : K ≤ K') :
    placeAlong w K ≤ placeAlong w K' := by
  rw [Matrix.le_iff, ← placeAlong_sub]
  exact posSemidef_placeAlong w (Matrix.le_iff.mp h)

variable [∀ v, Nonempty (X v)]

omit [∀ v, Fintype (X v)] in
/-- When every basis type is nonempty, placement along an injection is injective. -/
theorem placeAlong_injective : Function.Injective (placeAlong (X := X) w) :=
  fun _ _ h ↦ (reindex _ _).injective (place_injective _ h)

omit [∀ v, Fintype (X v)] in
@[simp]
theorem placeAlong_inj {K K' : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ} :
    placeAlong w K = placeAlong w K' ↔ K = K' :=
  (placeAlong_injective w).eq_iff

variable [DecidableEq W] in
/-- When every basis type is nonempty, placement along an injection preserves the norm. -/
theorem norm_placeAlong (K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ) :
    ‖placeAlong w K‖ = ‖K‖ := by
  classical
  rw [placeAlong, norm_place, Matrix.l2_opNorm_reindex_equiv]

omit [∀ v, Fintype (X v)] in
theorem posSemidef_placeAlong_iff [∀ v, Finite (X v)]
    {K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ} :
    (placeAlong w K).PosSemidef ↔ K.PosSemidef := by
  rw [placeAlong, posSemidef_place_iff, reindex_apply, posSemidef_submatrix_equiv]

omit [∀ v, Fintype (X v)] in
theorem placeAlong_le_placeAlong_iff [∀ v, Finite (X v)]
    {K K' : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ} :
    placeAlong w K ≤ placeAlong w K' ↔ K ≤ K' := by
  rw [Matrix.le_iff, Matrix.le_iff, ← placeAlong_sub, posSemidef_placeAlong_iff]

/-- When every basis type is nonempty, a matrix placed along an injection is unitary exactly
when the matrix is. -/
theorem placeAlong_mem_unitaryGroup_iff [DecidableEq W]
    {K : Matrix (Config fun u ↦ X (w u)) (Config fun u ↦ X (w u)) ℂ} :
    placeAlong w K ∈ unitaryGroup (Config X) ℂ ↔ K ∈ unitaryGroup _ ℂ := by
  refine ⟨fun h ↦ ?_, placeAlong_mem_unitaryGroup w⟩
  rw [mem_unitaryGroup_iff] at h ⊢
  apply placeAlong_injective w
  rw [placeAlong_mul, placeAlong_one, star_eq_conjTranspose, placeAlong_conjTranspose,
    ← star_eq_conjTranspose, h]

end Order

/-! ### Regions, bijections and composition -/

section Composition

/-- Placing along the inclusion of a region is placing on the region. -/
theorem placeAlong_subtype (D : Finset V) (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    placeAlong (Function.Embedding.subtype (· ∈ D)) K = place D K := by
  ext σ τ
  refine (placeAlong_apply (Function.Embedding.subtype (· ∈ D)) K σ τ).trans ?_
  rw [place_apply]
  refine if_congr ⟨fun h v hv ↦ h v fun u hu ↦ hv (hu ▸ u.2), fun h v hv ↦ h v fun hvD ↦
    hv ⟨v, hvD⟩ rfl⟩ rfl rfl

/-- Placing along a bijection of the sites relabels the configurations. -/
theorem placeAlong_equiv (e : W ≃ V)
    (K : Matrix (Config fun u ↦ X (e u)) (Config fun u ↦ X (e u)) ℂ) :
    placeAlong e.toEmbedding K =
      reindex (siteConfigurationEquiv e fun u ↦ Equiv.refl (X (e u)))
        (siteConfigurationEquiv e fun u ↦ Equiv.refl (X (e u))) K := by
  ext σ τ
  rw [placeAlong_apply, ite_eq_left fun v hv ↦ absurd (e.apply_symm_apply v) (hv (e.symm v)),
    reindex_apply, submatrix_apply]
  rfl

/-- Placing along the identity of the sites changes nothing. -/
@[simp]
theorem placeAlong_refl (K : Matrix (Config X) (Config X) ℂ) :
    placeAlong (Function.Embedding.refl V) K = K := by
  ext σ τ
  refine (placeAlong_apply (Function.Embedding.refl V) K σ τ).trans ?_
  rw [ite_eq_left fun v hv ↦ absurd rfl (hv v)]
  rfl

/-- **Composition.** Placing along `w'` and then along `w` is placing along `w ∘ w'`. -/
theorem placeAlong_placeAlong [DecidableEq W] {W' : Type*} [Fintype W'] (w' : W' ↪ W)
    (K : Matrix (Config fun u ↦ X (w (w' u))) (Config fun u ↦ X (w (w' u))) ℂ) :
    placeAlong w (placeAlong (X := fun u ↦ X (w u)) w' K) = placeAlong (w'.trans w) K := by
  ext σ τ
  rw [placeAlong_apply, placeAlong_apply]
  refine Eq.trans ?_ (placeAlong_apply (w'.trans w) K σ τ).symm
  simp only [Function.Embedding.trans_apply]
  by_cases h : ∀ v, (∀ u, w (w' u) ≠ v) → σ v = τ v
  · rw [ite_eq_left h, ite_eq_left fun v hv ↦ h v fun u hu ↦ hv _ hu, ite_eq_left fun u hu ↦
      h _ fun u' hu' ↦ hu u' (w.injective hu')]
    rfl
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨v, hv, hne⟩ := h
    split_ifs with h1 h2
    · obtain ⟨u, rfl⟩ : ∃ u, w u = v := by
        by_contra! hr
        exact hne (h1 v hr)
      exact absurd (h2 u fun u' hu' ↦ hv u' (by rw [hu'])) hne
    · rfl
    · rfl

/-- A product operator placed along an injection is the product operator that is the
on-site matrix `m u` at the site `w u` and the identity outside the image. -/
theorem placeAlong_prodOp (m : (u : W) → Matrix (X (w u)) (X (w u)) ℂ)
    (m' : (v : V) → Matrix (X v) (X v) ℂ) (hm : ∀ u, m' (w u) = m u)
    (hm' : ∀ v, (∀ u, w u ≠ v) → m' v = 1) :
    placeAlong w (prodOp m) = prodOp m' := by
  ext σ τ
  rw [placeAlong_apply, prodOp_apply, prodOp_apply,
    ← Finset.prod_mul_prod_compl (Finset.univ.map w), Finset.prod_map]
  have hout (v : V) (hv : v ∈ (Finset.univ.map w)ᶜ) : ∀ u, w u ≠ v := fun u hu ↦
    Finset.mem_compl.mp hv (hu ▸ Finset.mem_map_of_mem w (Finset.mem_univ u))
  by_cases h : ∀ v, (∀ u, w u ≠ v) → σ v = τ v
  · rw [ite_eq_left h, Finset.prod_eq_one (s := (Finset.univ.map w)ᶜ) fun v hv ↦ by
      rw [hm' v (hout v hv), h v (hout v hv), one_apply_eq], mul_one]
    exact Finset.prod_congr rfl fun u _ ↦ by rw [hm u]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨v, hv, hne⟩ := h
    have hvc : v ∈ (Finset.univ.map w)ᶜ := Finset.mem_compl.mpr fun hmem ↦ by
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hmem
      exact hv u rfl
    rw [Finset.prod_eq_zero hvc (by rw [hm' v hv, one_apply_ne hne]), mul_zero]

end Composition

/-! ### A matrix at one site -/

section Site

variable (v : V) (p p' : Matrix (X v) (X v) ℂ)

/-- **A matrix at one site.** A matrix `p` on the basis `X v` at the site `v`, acting as `p` at
`v` and as the identity elsewhere: the placement along the inclusion of the site. -/
noncomputable def placeAt : Matrix (Config X) (Config X) ℂ :=
  placeAlong (Function.Embedding.punit v : Unit ↪ V)
    (reindex (Equiv.funUnique Unit (X v)).symm (Equiv.funUnique Unit (X v)).symm p)

/-- Entries of a matrix at one site. -/
theorem placeAt_apply (σ τ : Config X) :
    placeAt v p σ τ = if ∀ u, u ≠ v → σ u = τ u then p (σ v) (τ v) else 0 := by
  refine (placeAlong_apply (X := X) (Function.Embedding.punit v : Unit ↪ V) _ σ τ).trans ?_
  refine if_congr ⟨fun h u hu ↦ h u fun _ h' ↦ hu h'.symm, fun h u hu ↦ h u fun h' ↦
    hu () h'.symm⟩ rfl rfl

theorem placeAt_add : placeAt v (p + p') = placeAt v p + placeAt v p' :=
  placeAlong_add (X := X) (Function.Embedding.punit v : Unit ↪ V) _ _

theorem placeAt_sub : placeAt v (p - p') = placeAt v p - placeAt v p' :=
  placeAlong_sub (X := X) (Function.Embedding.punit v : Unit ↪ V) _ _

theorem placeAt_neg : placeAt v (-p) = -placeAt v p := by
  ext σ τ
  rw [Matrix.neg_apply, placeAt_apply, placeAt_apply]
  split_ifs <;> simp

/-- A diagonal matrix at one site is the diagonal matrix of its entry at the site. -/
theorem placeAt_diagonal (f : X v → ℂ) :
    placeAt v (diagonal f) = diagonal fun σ : Config X ↦ f (σ v) := by
  ext σ τ
  rw [placeAt_apply, diagonal_apply, diagonal_apply]
  by_cases hστ : σ = τ
  · subst hστ
    simp
  · simp only [hστ, ↓reduceIte]
    split_ifs with h h'
    · exact absurd (funext fun u ↦ if hu : u = v then hu ▸ h' else h u hu) hστ
    · rfl
    · rfl

theorem placeAt_smul (c : ℂ) : placeAt v (c • p) = c • placeAt v p :=
  placeAlong_smul (X := X) (Function.Embedding.punit v : Unit ↪ V) _ c

theorem placeAt_conjTranspose : placeAt v pᴴ = (placeAt v p)ᴴ :=
  placeAlong_conjTranspose (X := X) (Function.Embedding.punit v : Unit ↪ V) _

@[simp]
theorem placeAt_one : placeAt v (1 : Matrix (X v) (X v) ℂ) = 1 := by
  classical
  rw [placeAt, reindex_apply, submatrix_one_equiv]
  exact placeAlong_one (X := X) (Function.Embedding.punit v : Unit ↪ V)

variable {v p} in
/-- A Hermitian matrix at one site is Hermitian. -/
theorem isHermitian_placeAt (hp : p.IsHermitian) : (placeAt v p).IsHermitian :=
  isHermitian_placeAlong _ (hp.reindex _)

/-- A matrix on the configurations of the region `{v}`, read through the basis of `v`
(`ManyBody.siteEquiv`) and placed on `{v}`, is the matrix at the site `v`. -/
theorem place_siteEquiv_eq_placeAt :
    place {v} (p.submatrix (siteEquiv X v) (siteEquiv X v)) = placeAt v p := by
  ext σ τ
  rw [placeAt_apply, place_apply]
  simp only [Finset.mem_singleton]
  rfl

/-- A matrix at one site is the product operator with that matrix at the site and the identity
at the other sites. -/
theorem placeAt_eq_prodOp :
    placeAt v p = prodOp (Function.update (fun s ↦ (1 : Matrix (X s) (X s) ℂ)) v p) := by
  ext x y
  rw [placeAt_apply, prodOp_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    Function.update_self]
  have h : ∀ s ∈ Finset.univ.erase v,
      Function.update (fun s ↦ (1 : Matrix (X s) (X s) ℂ)) v p s (x s) (y s) =
        if x s = y s then 1 else 0 := fun s hs ↦ by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs), one_apply]
  rw [Finset.prod_congr rfl h, Finset.prod_boole]
  simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
  split_ifs <;> simp

variable [∀ v, Fintype (X v)]

theorem placeAt_mul : placeAt v (p * p') = placeAt v p * placeAt v p' := by
  classical
  rw [placeAt, placeAt, placeAt, reindex_apply, reindex_apply, reindex_apply,
    ← submatrix_mul_equiv (e₂ := (Equiv.funUnique Unit (X v)).symm.symm)]
  exact placeAlong_mul (X := X) (Function.Embedding.punit v : Unit ↪ V) _ _

variable {v p} in
/-- A unitary matrix at one site is unitary. -/
theorem placeAt_mem_unitaryGroup (hp : p ∈ unitaryGroup (X v) ℂ) :
    placeAt v p ∈ unitaryGroup (Config X) ℂ := by
  rw [← place_siteEquiv_eq_placeAt]
  exact place_mem_unitaryGroup (submatrix_equiv_mem_unitary.mpr hp)

/-- A matrix at one site acts on a vector through the basis of that site. -/
theorem placeAt_mulVec_apply (ψ : Config X → ℂ) (y : Config X) :
    (placeAt v p *ᵥ ψ) y = ∑ b : X v, p (y v) b * ψ (Function.update y v b) := by
  rw [← place_siteEquiv_eq_placeAt, place_mulVec_apply, ← (siteEquiv X v).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [submatrix_apply, Equiv.apply_symm_apply]
  have hcut : (cutEquiv X {v}).symm ((siteEquiv X v).symm b, (cutEquiv X {v} y).2) =
      Function.update y v b := by
    funext u
    by_cases hu : u = v
    · subst hu
      rw [cutEquiv_symm_apply_mem _ _ (Finset.mem_singleton_self u), Function.update_self]
      rfl
    · rw [cutEquiv_symm_apply_not_mem _ _ (by simpa using hu), Function.update_of_ne hu]
      rfl
  rw [hcut]
  rfl

/-- A matrix at the site `v` is supported on `{v}`. -/
theorem placeAt_mem_supportedOperators : placeAt v p ∈ supportedOperators X {v} := by
  have hmap : Finset.univ.map (Function.Embedding.punit v : Unit ↪ V) = {v} := by
    ext u
    simp [Function.Embedding.punit, eq_comm]
  rw [← hmap]
  exact placeAlong_mem_supportedOperators (X := X) (Function.Embedding.punit v : Unit ↪ V) _

/-- A matrix at one site has at most its norm. -/
theorem norm_placeAt_le : ‖placeAt v p‖ ≤ ‖p‖ :=
  (norm_placeAlong_le _ _).trans (Matrix.l2_opNorm_reindex_equiv _ p).le

omit [∀ v, Fintype (X v)] in
variable {v p} in
/-- A positive semidefinite matrix at one site is positive semidefinite. -/
theorem posSemidef_placeAt [∀ v, Finite (X v)] (hp : p.PosSemidef) :
    (placeAt v p).PosSemidef :=
  posSemidef_placeAlong _ (by rw [reindex_apply]; exact hp.submatrix _)

omit [∀ v, Fintype (X v)] in
variable {v p p'} in
/-- Placing at one site is monotone. -/
theorem placeAt_le_placeAt [∀ v, Finite (X v)] (h : p ≤ p') : placeAt v p ≤ placeAt v p' := by
  rw [Matrix.le_iff, ← placeAt_sub]
  exact posSemidef_placeAt (Matrix.le_iff.mp h)

end Site

/-! ### Identical sites -/

section SitePermutation

variable {α : Type*} [Fintype α] [DecidableEq α] (w : W ↪ V)

/-- **The action on a vector, on identical sites.** A matrix placed along `w` maps `ψ` to the
vector whose component at `σ` is `∑ₐ K (σ ∘ w, a) ψ (σ')`, where `σ'` is `a` on the image of `w`
and `σ` outside it. -/
theorem placeAlong_mulVec_apply [DecidableEq W] (K : Matrix (W → α) (W → α) ℂ)
    (ψ : (V → α) → ℂ) (σ : V → α) :
    (placeAlong (X := fun _ ↦ α) w K *ᵥ ψ) σ =
      ∑ a, K (σ ∘ w) a * ψ (Function.extend w a σ) := by
  refine (placeAlong_mulVec_apply_of (X := fun _ ↦ α) w K ψ σ (fun a ↦ Function.extend w a σ)
    (fun a u ↦ w.injective.extend_apply a σ u) fun a v hv ↦ ?_).trans rfl
  exact Function.extend_apply' _ _ _ fun ⟨u, hu⟩ ↦ hv u hu

/-- Entries of a product with a matrix placed along `w`, as a sum over the configurations of
`W`. -/
theorem mul_placeAlong_apply [DecidableEq W] (Y : Matrix (V → α) (V → α) ℂ)
    (K : Matrix (W → α) (W → α) ℂ) (σ τ : V → α) :
    (Y * placeAlong (X := fun _ ↦ α) w K) σ τ =
      ∑ a, Y σ (Function.extend w a τ) * K a (τ ∘ w) := by
  have h := placeAlong_mulVec_apply w Kᴴ (fun ρ ↦ star (Y σ ρ)) τ
  rw [placeAlong_conjTranspose] at h
  have h' : (Y * placeAlong (X := fun _ ↦ α) w K) σ τ =
      star (((placeAlong (X := fun _ ↦ α) w K)ᴴ *ᵥ fun ρ ↦ star (Y σ ρ)) τ) := by
    simp only [mul_apply, mulVec, dotProduct, conjTranspose_apply, star_sum, star_mul',
      star_star, mul_comm]
  rw [h', h, star_sum]
  simp only [conjTranspose_apply, star_mul', star_star, mul_comm]

omit [Fintype α] in
/-- Relabelling the configurations along a permutation `π` of the sites moves a placement along
`w` to the placement along `π ∘ w`. -/
theorem placeAlong_submatrix_comp (π : Equiv.Perm V) (K : Matrix (W → α) (W → α) ℂ) :
    (placeAlong (X := fun _ ↦ α) w K).submatrix (· ∘ π) (· ∘ π) =
      placeAlong (X := fun _ ↦ α) (w.trans π.toEmbedding) K := by
  ext σ τ
  rw [submatrix_apply, placeAlong_apply, placeAlong_apply]
  simp only [Function.comp_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  refine if_congr ⟨fun h v hv ↦ ?_, fun h v hv ↦ h (π v) fun u hu ↦ hv u (π.injective hu)⟩
    rfl rfl
  have h' := h (π.symm v) fun u hu ↦ hv u (by rw [hu, Equiv.apply_symm_apply])
  rwa [Equiv.apply_symm_apply] at h'

/-- **Moving a placement by a permutation of the sites.** Conjugating a matrix placed along `w`
by the operator moving the content of every site `v` to `π v` gives the matrix placed along
`π ∘ w`. -/
theorem sitePermOp_mul_placeAlong_mul_conjTranspose (π : Equiv.Perm V)
    (K : Matrix (W → α) (W → α) ℂ) :
    sitePermOp π * placeAlong (X := fun _ ↦ α) w K * (sitePermOp π)ᴴ =
      placeAlong (X := fun _ ↦ α) (w.trans π.toEmbedding) K := by
  have he : ⇑(siteConfigurationEquiv (X := fun _ : V ↦ α) (X' := fun _ : V ↦ α) π
      fun _ ↦ Equiv.refl α).symm = (· ∘ π) :=
    funext fun σ ↦ funext fun v ↦ siteConfigurationEquiv_symm_apply π _ σ v
  rw [sitePermOp_mul_mul_conjTranspose, reindex_apply, he, placeAlong_submatrix_comp]

omit [Fintype α] in
/-- The permutation operator of a permutation `π` of the sites `W`, placed along `w`, is the
permutation operator of the permutation of `V` that is `π` on the image of `w` and the identity
elsewhere. -/
theorem placeAlong_sitePermOp (π : Equiv.Perm W) :
    placeAlong (X := fun _ ↦ α) w (sitePermOp π) = sitePermOp (π.viaEmbedding w) := by
  ext σ τ
  rw [placeAlong_apply, sitePermOp_apply, sitePermOp_apply]
  by_cases h1 : ∀ v, (∀ u, w u ≠ v) → σ v = τ v
  · rw [ite_eq_left h1]
    refine if_congr ⟨fun h ↦ funext fun v ↦ ?_, fun h ↦ funext fun u ↦ ?_⟩ rfl rfl
    · by_cases hv : v ∈ Set.range w
      · obtain ⟨u, rfl⟩ := hv
        rw [Function.comp_apply, Equiv.Perm.viaEmbedding_apply]
        exact congrFun h u
      · rw [Function.comp_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hv]
        exact (h1 v fun u hu ↦ hv ⟨u, hu⟩).symm
    · have h' := congrFun h (w u)
      rwa [Function.comp_apply, Equiv.Perm.viaEmbedding_apply] at h'
  · rw [ite_eq_right h1, ite_eq_right]
    rintro rfl
    refine h1 fun v hv ↦ ?_
    rw [Function.comp_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _
      fun ⟨u, hu⟩ ↦ hv u hu]

end SitePermutation

end ManyBody
