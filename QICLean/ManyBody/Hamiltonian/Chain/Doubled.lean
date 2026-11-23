/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Dist
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.Analysis.Norm.MatrixKroneckerContraction
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.KroneckerSum
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.ConfigurationMap
import QICLean.ManyBody.Sites.PairSwapPermutation
import QICLean.ManyBody.Sites.ReplicaSwap

/-!
# Two copies of a chain Hamiltonian and their exchange on a region

The doubled interaction `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ` (`ManyBody.Interaction.doubled`) lives on the
system with basis `Fin q × Fin q` at every site. Encoding each pair in `Fin (q * q)` by
`finProdFinEquiv`, a relabelling of the basis at every site, gives an interaction with local
dimension `q * q`, `ManyBody.Interaction.doubledFin`, the alphabet of the chain and domain models.
Each term keeps its support, and the Hamiltonian is `H ⊗ 1 + 1 ⊗ H` in the coordinates that pair
the two configuration values at every site (`Equiv.arrowProdEquivProdArrow`) and encode each
pair by `finProdFinEquiv`.

Let `F` be the exchange `ManyBody.pairSwapOp D` of the two copies on a region `D`, in these
coordinates. For a gapped ground vector `Ω` of a chain Hamiltonian `H`, the tensor square of `Ω`
and its image under `F` are gapped ground vectors of `K = H ⊗ 1 + 1 ⊗ H` and of `F K Fᴴ`, of
energy `2 E₀` and with the same gap. A term supported inside `D` or disjoint from `D` is fixed by
the conjugation with `F`, so `F K Fᴴ - K` is the sum, over the supports crossing `D` and the two
copies, of the differences `F T Fᴴ - T` of the terms `T` of one copy; each is Hermitian, supported
on its support and of norm at most `2J`. On the chain there are at most `N_R / 2` crossing
supports for each boundary edge of `D`, with `N_R = 2 · 2^{2R}`, so
`‖F K Fᴴ - K‖ ≤ 2 J N_R |∂D|`; on a finite domain `Λ ⊂ ℤ` twice their number is at most
`N_R |Λ|`. Zero local dimension and empty boundaries are included.

## Main definitions

* `ManyBody.Interaction.doubledFin` — the doubled interaction with local alphabet `Fin (q * q)`.

## Main results

* `ManyBody.Interaction.hamiltonian_doubledFin` — its Hamiltonian is the reindexed `H ⊗ 1 + 1 ⊗ H`.
* `ManyBody.ChainInteraction.isGapped_doubledFin_and_conj_pairSwapOp_of_isGapped` — the doubled
  ground vectors and their gap.
* `ManyBody.ChainInteraction.partialSwap_term_difference_spec`,
  `ManyBody.DomainInteraction.partialSwap_term_difference_spec` — the differences of the terms.
* `ManyBody.ChainInteraction.partialSwap_difference_eq_sum_crossing`,
  `ManyBody.DomainInteraction.partialSwap_difference_eq_sum_crossing` — `F K Fᴴ - K` as a sum
  over the crossing supports, with their number.
* `ManyBody.ChainInteraction.partialSwap_boundary_spec` — the support and the norm of
  `F K Fᴴ - K`.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

namespace ManyBody

section Doubled

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} {S : ι → Finset V} {q : ℕ}

/-- The doubled interaction `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ` with the two copies of every site paired into
the local alphabet `Fin (q * q)`: the relabelling of `Interaction.doubled` along
`finProdFinEquiv` at every site. Each term keeps its support. -/
noncomputable def Interaction.doubledFin
    (Φ : Interaction (fun _ : V ↦ Fin q) S) :
    Interaction (fun _ : V ↦ Fin (q * q)) S :=
  Φ.doubled.relabel (X' := fun _ : V ↦ Fin (q * q)) (Equiv.refl V) (fun _ ↦ finProdFinEquiv) S
    fun _ _ ↦ Iff.rfl

/-- The paired doubled term with index `i` is `hᵢ ⊗ 1 + 1 ⊗ hᵢ` in the paired coordinates. -/
theorem Interaction.doubledFin_term
    (Φ : Interaction (fun _ : V ↦ Fin q) S) (i : ι) :
    Φ.doubledFin.term i = Matrix.reindex
      ((Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
        (Equiv.arrowCongr (Equiv.refl V) finProdFinEquiv))
      ((Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
        (Equiv.arrowCongr (Equiv.refl V) finProdFinEquiv)) (Φ.term i ⊗ₖ 1 + 1 ⊗ₖ Φ.term i) :=
  rfl

/-- Summing the paired doubled terms gives exactly the sum of the two copies of `H`, after
grouping their local coordinates at each site. -/
theorem Interaction.hamiltonian_doubledFin [Fintype ι]
    (Φ : Interaction (fun _ : V ↦ Fin q) S) :
    Φ.doubledFin.hamiltonian = Matrix.reindex
      ((Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
        (Equiv.arrowCongr (Equiv.refl V) finProdFinEquiv))
      ((Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
        (Equiv.arrowCongr (Equiv.refl V) finProdFinEquiv))
        (Φ.hamiltonian ⊗ₖ 1 + 1 ⊗ₖ Φ.hamiltonian) := by
  refine (Interaction.hamiltonian_relabel _ _ _ _ _).trans ?_
  rw [Interaction.hamiltonian_doubled]
  ext x y
  simp [siteConfigurationEquiv, Matrix.doubledHamiltonian]

end Doubled

section Chain

/-- For a gapped ground vector `Ω` of `H` with gap `Δ > 0`, the paired tensor square `Ψ` of `Ω`
is a gapped ground vector of the doubled Hamiltonian `K`, and its image `F Ψ` under the exchange
`F` of the two copies on `D` is one of `F K Fᴴ`, both of energy `2 E₀` and gap `Δ`. -/
theorem ChainInteraction.isGapped_doubledFin_and_conj_pairSwapOp_of_isGapped
    {L q R : ℕ} {E₀ Δ : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin L)) {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ) :
    let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
    let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
    let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (ψ₀ ∘ e.symm)
    let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
    (‖Ψ‖ = 1 ∧ IsGapped h.doubledFin.hamiltonian (2 * E₀) Δ ∧
      groundSpace h.doubledFin.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ}) ∧
      (‖Φ‖ = 1 ∧ IsGapped (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) Δ ∧
        groundSpace (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) = Submodule.span ℂ {Φ}) := by
  classical
  let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
  let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
  let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
  let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
  let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2 (ψ₀ ∘ e.symm)
  let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
    WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
  change (‖Ψ‖ = 1 ∧ IsGapped h.doubledFin.hamiltonian (2 * E₀) Δ ∧
    groundSpace h.doubledFin.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ}) ∧
    (‖Φ‖ = 1 ∧ IsGapped (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) Δ ∧
      groundSpace (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) = Submodule.span ℂ {Φ})
  have hH := (Interaction.isHermitian_hamiltonian hh)
  have hgK := hgap.kronecker_add hH hH hgap (Or.inl hΔ.le)
  have hsK := groundSpace_kronecker_add_eq_span hH hH hgap hgap hΔ.le hΔ.le hspan hspan
  rw [min_self] at hgK
  have hgapD : IsGapped h.doubledFin.hamiltonian (2 * E₀) Δ := by
    rw [h.hamiltonian_doubledFin, isGapped_reindex_iff, two_mul]
    exact hgK
  have hspanD : groundSpace h.doubledFin.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ} := by
    rw [h.hamiltonian_doubledFin, two_mul]
    exact groundSpace_reindex_eq_span e hsK
  have hΩsum : ∑ i, ‖WithLp.ofLp Ω i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hΩ]
    norm_num
  have hΨ : ‖Ψ‖ = 1 := by
    have hi := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
      (WithLp.toLp 2 ψ₀)
    change ‖Ψ‖ = ‖WithLp.toLp 2 ψ₀‖ at hi
    exact hi.trans (Matrix.norm_doubledVector hΩsum)
  have hF : F ∈ Matrix.unitaryGroup _ ℂ :=
    Matrix.reindex_mem_unitaryGroup e _
      (Matrix.reindex_mem_unitaryGroup _ _ (pairSwapOp_mem_unitaryGroup D))
  refine ⟨⟨hΨ, hgapD, hspanD⟩, ?_⟩
  have hΦ : Matrix.toEuclideanLin F Ψ = Φ := rfl
  have hΦn : ‖Φ‖ = 1 := by
    change ‖WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)‖ = 1
    rw [Matrix.norm_toLp_mulVec_of_unitary hF]
    exact hΨ
  rw [← hΦ]
  exact ⟨by rw [hΦ]; exact hΦn, (isGapped_unitary_conj_iff hF).mpr hgapD,
    groundSpace_unitary_conj_eq_span hF hspanD⟩

/-- For the term `T` of one copy with support `X`, the difference `F T Fᴴ - T` is Hermitian,
supported on `X` and of norm at most `2J`. -/
theorem ChainInteraction.partialSwap_term_difference_spec
    {L q R : ℕ} {J : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin L)) (X : ChainSupport L R) (b : Bool) :
    let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
    let T := Matrix.reindex e e
      (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let K := F * T * Fᴴ - T
    IsSupportedOn (X := fun _ ↦ Fin (q * q)) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
  classical
  let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
  let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
  let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
  have hterm := h.mem X
  have hone := one_mem (supportedOperators (fun _ ↦ Fin q) X.1)
  have hF : ‖F‖ ≤ 1 := by
    simpa only [F, Matrix.l2_opNorm_reindex_equiv] using
      norm_pairSwapOp_le_one (X := fun _ : Fin L ↦ Fin q) D
  have hgeneral (U V : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hU : U ∈ supportedOperators (fun _ ↦ Fin q) X.1)
      (hV : V ∈ supportedOperators (fun _ ↦ Fin q) X.1)
      (hUVherm : (U ⊗ₖ V).IsHermitian) (hUVnorm : ‖U ⊗ₖ V‖ ≤ J) :
      let T := Matrix.reindex e e (U ⊗ₖ V)
      let K := F * T * Fᴴ - T
      IsSupportedOn (X := fun _ ↦ Fin (q * q)) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
    have hT : Matrix.reindex e e (U ⊗ₖ V) ∈
        supportedOperators (fun _ ↦ Fin (q * q)) X.1 := by
      have h := reindex_siteConfigurationEquiv_mem_supportedOperators
        (Equiv.refl (Fin L)) (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv)
        (fun _ ↦ Iff.rfl) (reindex_kronecker_mem_supportedOperators hU hV)
      rw [Finset.union_self] at h
      convert h using 1
      ext x y
      simp [e, pr, siteConfigurationEquiv]
    -- in the coordinates pairing the two copies of every site, `F` is the exchange of the
    -- copies on `D`, which keeps the support of the paired product `U ⊗ V`
    have hFT : F * Matrix.reindex e e (U ⊗ₖ V) * Fᴴ ∈
        supportedOperators (fun _ ↦ Fin (q * q)) X.1 := by
      have h := reindex_siteConfigurationEquiv_mem_supportedOperators
        (Equiv.refl (Fin L)) (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv)
        (fun _ ↦ Iff.rfl) (pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (reindex_kronecker_mem_supportedOperators hU hV))
      rw [Finset.union_self] at h
      convert h using 1
      let g := siteConfigurationEquiv (X' := fun _ : Fin L ↦ Fin (q * q))
        (Equiv.refl (Fin L)) fun _ ↦ finProdFinEquiv
      change Matrix.reindex g g (pairSwapOp D) *
          Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (U ⊗ₖ V)) *
          (Matrix.reindex g g (pairSwapOp D))ᴴ = _
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv]
      rfl
    refine ⟨(Subalgebra.toSubmodule
        (supportedOperators (fun _ ↦ Fin (q * q)) X.1).toSubalgebra).sub_mem hFT hT,
      ?_, ?_⟩
    · have hTherm := hUVherm.reindex e
      exact (Matrix.isHermitian_mul_mul_conjTranspose F hTherm).sub hTherm
    · have hTnorm : ‖Matrix.reindex e e (U ⊗ₖ V)‖ ≤ J := by
        simpa only [Matrix.l2_opNorm_reindex_equiv] using hUVnorm
      have hconj : ‖F * Matrix.reindex e e (U ⊗ₖ V) * Fᴴ‖ ≤ J := by
        simpa only [one_mul, mul_one] using
          norm_mul_le_of_le (norm_mul_le_of_le hF hTnorm)
            ((Matrix.l2_opNorm_conjTranspose F).trans_le hF)
      exact (norm_sub_le _ _).trans ((add_le_add hconj hTnorm).trans_eq (by ring))
  cases b
  · apply hgeneral (h.term X) 1 hterm hone
    · change (h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))ᴴ = _
      rw [conjTranspose_kronecker, hh X, conjTranspose_one]
    · exact (Matrix.l2_opNorm_kronecker_one_le _).trans (hhJ X)
  · apply hgeneral 1 (h.term X) hone hterm
    · change ((1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X)ᴴ = _
      rw [conjTranspose_kronecker, hh X, conjTranspose_one]
    · exact (Matrix.l2_opNorm_one_kronecker_le _).trans (hhJ X)

/-- `F K Fᴴ - K` is the sum of the differences `F T Fᴴ - T` of the terms of both copies over
the supports `C` crossing `D`, and `2 |C| ≤ N_R |∂D|`. -/
theorem ChainInteraction.partialSwap_difference_eq_sum_crossing
    {L q R : ℕ} (h : ChainInteraction L q R) (D : Finset (Fin L)) :
    let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
    let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
      (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let C := crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    (F * h.doubledFin.hamiltonian * Fᴴ - h.doubledFin.hamiltonian =
      ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * (boundaryEdges L D).card := by
  classical
  let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
  let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
  let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  let C := crossingTerms (fun X : ChainSupport L R ↦ X.1) D
  change (F * h.doubledFin.hamiltonian * Fᴴ - h.doubledFin.hamiltonian =
    ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * (boundaryEdges L D).card
  have hpair (X : ChainSupport L R) : h.doubledFin.term X = ∑ b : Bool, T X b := by
    rw [Fintype.sum_bool]
    change Matrix.reindex e e (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X) =
      Matrix.reindex e e (1 ⊗ₖ h.term X) + Matrix.reindex e e (h.term X ⊗ₖ 1)
    simpa only [Matrix.coe_reindexAddEquiv] using
      ((Matrix.reindexAddEquiv ℂ e e).map_add (h.term X ⊗ₖ 1) (1 ⊗ₖ h.term X)).trans
        (add_comm _ _)
  have hsum : h.doubledFin.hamiltonian = ∑ X, ∑ b : Bool, T X b :=
    Finset.sum_congr rfl (fun X _ ↦ hpair X)
  let δ : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ →ₗ[ℂ]
      Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ :=
    LinearMap.mulLeftRight ℂ (F, Fᴴ) - LinearMap.id
  have hcancel (X : ChainSupport L R) (hX : X ∉ C) : δ (∑ b : Bool, T X b) = 0 := by
    have hnot : ¬ ((∃ v ∈ X.1, v ∈ D) ∧ ∃ v ∈ X.1, v ∉ D) := by
      simpa only [C, crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        using hX
    have hside : X.1 ⊆ D ∨ Disjoint X.1 D := by
      rcases not_and_or.mp hnot with hi | ho
      · exact Or.inr (Finset.disjoint_left.mpr (fun x hx hxD ↦ hi ⟨x, hx, hxD⟩))
      · exact Or.inl (by
          intro x hx
          by_contra hxD
          exact ho ⟨x, hx, hxD⟩)
    rw [← hpair X]
    change F * Matrix.reindex e e (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex e e (doubledHamiltonian (h.term X)) = 0
    apply sub_eq_zero.mpr
    -- the exchange on `D` fixes a doubled term supported inside or outside `D`
    have hfix : pairSwapOp D *
        Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X)) *
        (pairSwapOp D)ᴴ = Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X)) :=
      hside.elim (fun hs ↦ pairSwapOp_conj_doubled_of_subset hs (h.mem X))
        (fun hs ↦ pairSwapOp_mul_mul_conjTranspose_of_disjoint hs
          (reindex_doubledHamiltonian_mem_supportedOperators (h.mem X)))
    let g := siteConfigurationEquiv (X' := fun _ : Fin L ↦ Fin (q * q))
      (Equiv.refl (Fin L)) fun _ ↦ finProdFinEquiv
    change Matrix.reindex g g (pairSwapOp D) *
        Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X))) *
        (Matrix.reindex g g (pairSwapOp D))ᴴ =
      Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X)))
    simpa only [Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv] using congrArg (Matrix.reindex g g) hfix
  refine ⟨?_, ?_⟩
  · change δ h.doubledFin.hamiltonian = ∑ X ∈ C, ∑ b : Bool, δ (T X b)
    rw [hsum, map_sum]
    simp only [map_sum]
    symm
    apply Finset.sum_subset (Finset.subset_univ C)
    intro X _ hX
    simpa only [map_sum] using hcancel X hX
  · calc
      C.card * 2 ≤ (2 ^ (2 * R) * (boundaryEdges L D).card) * 2 :=
        Nat.mul_le_mul_right 2 (card_crossingTerms_le_mul_card_boundaryEdges L R D)
      _ = chainCrossConst R * (boundaryEdges L D).card := by
        unfold chainCrossConst
        ring

/-- `F K Fᴴ - K` is supported on the union `Z` of the supports crossing `D`, every site of `Z`
lies within `R` of a boundary edge of `D`, and `‖F K Fᴴ - K‖ ≤ 2 J N_R |∂D|`. -/
theorem ChainInteraction.partialSwap_boundary_spec
    {L q R : ℕ} {J : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin L)) :
    let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
    let C := crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let K := F * h.doubledFin.hamiltonian * Fᴴ - h.doubledFin.hamiltonian
    IsSupportedOn (X := fun _ ↦ Fin (q * q)) K Z ∧
      (∀ x ∈ Z, ∃ p ∈ boundaryEdges L D, Nat.dist x.val p ≤ R) ∧
      ‖K‖ ≤ 2 * J * (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ) := by
  classical
  let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
  let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
  let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
  let C := crossingTerms (fun X : ChainSupport L R ↦ X.1) D
  let Z := C.biUnion (fun X ↦ X.1)
  let K := F * h.doubledFin.hamiltonian * Fᴴ - h.doubledFin.hamiltonian
  change IsSupportedOn (X := fun _ ↦ Fin (q * q)) K Z ∧
    (∀ x ∈ Z, ∃ p ∈ boundaryEdges L D, Nat.dist x.val p ≤ R) ∧
      ‖K‖ ≤ 2 * J * (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ)
  have hzone : ∀ x ∈ Z, ∃ p ∈ boundaryEdges L D, Nat.dist x.val p ≤ R := by
    intro x hx
    obtain ⟨X, hXC, hxX⟩ := Finset.mem_biUnion.mp hx
    have hsplit : (∃ v ∈ X.1, v ∈ D) ∧ ∃ v ∈ X.1, v ∉ D := by
      simpa only [C, crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        using hXC
    obtain ⟨p, hp, hwin⟩ := X.2.exists_boundary_window_of_split hsplit
    refine ⟨p, hp, ?_⟩
    have hxwin := mem_interval.mp (hwin hxX)
    simp only [Nat.dist]
    omega
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  change K = ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b) at hsum
  have hsupp : IsSupportedOn (X := fun _ ↦ Fin (q * q)) K Z := by
    change _ ∈ supportedOperators _ _
    rw [hsum]
    apply sum_mem
    intro X hXC
    apply sum_mem
    intro b _
    apply supportedOperators_mono
      (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem (fun X ↦ X.1) hXC))
    exact (h.partialSwap_term_difference_spec hh hhJ D X b).1
  have hnorm : ‖K‖ ≤ (C.card : ℝ) * (2 * (2 * J)) := by
    rw [hsum]
    calc
      _ ≤ ∑ X ∈ C, ‖∑ b : Bool, (F * T X b * Fᴴ - T X b)‖ := norm_sum_le _ _
      _ ≤ ∑ X ∈ C, ∑ b : Bool, ‖F * T X b * Fᴴ - T X b‖ :=
        Finset.sum_le_sum (fun X _ ↦ norm_sum_le _ _)
      _ ≤ ∑ _X ∈ C, ∑ _b : Bool, 2 * J := by
        apply Finset.sum_le_sum
        intro X _
        exact Finset.sum_le_sum (fun b _ ↦ (h.partialSwap_term_difference_spec hh hhJ D X b).2.2)
      _ = _ := by simp
  refine ⟨hsupp, hzone, ?_⟩
  by_cases hL : L = 0
  · have hb : boundaryEdges L D = ∅ := Finset.eq_empty_of_forall_notMem fun p hp ↦ by
      have := (mem_boundaryEdges.mp hp).1
      omega
    have hc : C.card = 0 := by
      change C.card * 2 ≤ chainCrossConst R * (boundaryEdges L D).card at hcount
      rw [hb] at hcount
      simp only [Finset.card_empty, mul_zero] at hcount
      omega
    simpa only [hc, Nat.cast_zero, zero_mul, hb, Finset.card_empty, mul_zero] using hnorm
  · let x : Fin L := ⟨0, Nat.pos_of_ne_zero hL⟩
    have hJ : 0 ≤ J := h.norm_bound_nonneg hhJ x
    have hc : (C.card : ℝ) * 2 ≤
        (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ) := by
      exact_mod_cast hcount
    calc
      ‖K‖ ≤ (C.card : ℝ) * (2 * (2 * J)) := hnorm
      _ = (2 * J) * ((C.card : ℝ) * 2) := by ring
      _ ≤ (2 * J) * ((chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

end Chain

section Domain

variable {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}

private theorem norm_bound_nonneg_of_support (h : DomainInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (X : DomainSupport Λ R) : 0 ≤ J :=
  h.norm_bound_nonneg hhJ (Classical.choose X.2.1)

/-- On a finite domain, for the term `T` of one copy with support `X`, the difference
`F T Fᴴ - T` is Hermitian, supported on `X` and of norm at most `2J`. -/
theorem DomainInteraction.partialSwap_term_difference_spec
    (h : DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (D : Finset (Fin Λ.card))
    (X : DomainSupport Λ R) (b : Bool) :
    let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
    let T := Matrix.reindex e e
      (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
    let K := F * T * Fᴴ - T
    IsSupportedOn (X := fun _ ↦ Fin (q * q)) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
  have hterm : (h.extend DomainSupport.toChainSupport
      DomainSupport.toChainSupport_injective (fun Y ↦ Y.1)
        fun _ ↦ subset_rfl).term X.toChainSupport = h.term X :=
    DomainSupport.toChainSupport_injective.extend_apply _ _ _
  have hs :=
    ChainInteraction.partialSwap_term_difference_spec
      (h.extend DomainSupport.toChainSupport DomainSupport.toChainSupport_injective
        (fun Y ↦ Y.1) fun _ ↦ subset_rfl)
      (Interaction.isHermitian_extend_term hh)
      (Interaction.norm_extend_term_le (norm_bound_nonneg_of_support h hhJ X) hhJ)
      D X.toChainSupport b
  rw [hterm] at hs
  simpa only [DomainSupport.toChainSupport] using hs

/-- On a finite domain `Λ`, `F K Fᴴ - K` is the sum of the differences of the terms of both
copies over the supports `C` crossing `D`, and `2 |C| ≤ N_R |Λ|`. -/
theorem DomainInteraction.partialSwap_difference_eq_sum_crossing
    (h : DomainInteraction Λ q R) (D : Finset (Fin Λ.card)) :
    let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
    let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
      (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
    let C := crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
    (F * h.doubledFin.hamiltonian * Fᴴ - h.doubledFin.hamiltonian =
      ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * Λ.card := by
  classical
  let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
  let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
  let F := Matrix.reindex e e (Matrix.reindex pr pr (pairSwapOp D))
  let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
  let C := crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
  let δ : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ →ₗ[ℂ]
      Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ :=
    LinearMap.mulLeftRight ℂ (F, Fᴴ) - LinearMap.id
  have hcancel (X : DomainSupport Λ R) (hX : X ∉ C) : δ (h.doubledFin.term X) = 0 := by
    have hside : X.1 ⊆ D ∨ Disjoint X.1 D := by
      simp only [C, crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
      simp only [Finset.disjoint_left]
      grind
    change F * Matrix.reindex e e (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex e e (doubledHamiltonian (h.term X)) = 0
    apply sub_eq_zero.mpr
    -- the exchange on `D` fixes a doubled term supported inside or outside `D`
    have hfix : pairSwapOp D *
        Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X)) *
        (pairSwapOp D)ᴴ = Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X)) :=
      hside.elim (fun hs ↦ pairSwapOp_conj_doubled_of_subset hs (h.mem X))
        (fun hs ↦ pairSwapOp_mul_mul_conjTranspose_of_disjoint hs
          (reindex_doubledHamiltonian_mem_supportedOperators (h.mem X)))
    let g := siteConfigurationEquiv (X' := fun _ : Fin Λ.card ↦ Fin (q * q))
      (Equiv.refl (Fin Λ.card)) fun _ ↦ finProdFinEquiv
    change Matrix.reindex g g (pairSwapOp D) *
        Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X))) *
        (Matrix.reindex g g (pairSwapOp D))ᴴ =
      Matrix.reindex g g (Matrix.reindex pr.symm pr.symm (doubledHamiltonian (h.term X)))
    simpa only [Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv] using congrArg (Matrix.reindex g g) hfix
  refine ⟨?_, card_domain_crossingTerms_mul_two_le Λ R D⟩
  change δ h.doubledFin.hamiltonian = ∑ X ∈ C, ∑ b : Bool, δ (T X b)
  change δ (∑ X, h.doubledFin.term X) = _
  rw [map_sum]
  calc
    _ = ∑ X ∈ C, δ (h.doubledFin.term X) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      exact fun X _ hX ↦ hcancel X hX
    _ = _ := by
      apply Finset.sum_congr rfl
      intro X _
      rw [← map_sum]
      congr 1
      rw [Fintype.sum_bool]
      change Matrix.reindex e e (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X) =
        Matrix.reindex e e (1 ⊗ₖ h.term X) + Matrix.reindex e e (h.term X ⊗ₖ 1)
      simpa only [Matrix.coe_reindexAddEquiv] using
        ((Matrix.reindexAddEquiv ℂ e e).map_add (h.term X ⊗ₖ 1) (1 ⊗ₖ h.term X)).trans
          (add_comm _ _)

end Domain

end ManyBody
