/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.PhysicalBufferUniform
import QICLean.Analysis.GaussianFilter.Reindex
import QICLean.Algebra.L2OpNormReindex
import QICLean.Entropy.FiniteProductSplitting
import QICLean.Entropy.ProductMarginals
import QICLean.Entropy.SumSitesProduct
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Sites.ReplicaSwap

/-!
# The two-sided Gaussian filter of the information reset

Let `Ω` be a gapped ground vector of a Hamiltonian `H` on the sites `V`, and let `R, C` be
disjoint regions with `I_Ω(R : C) ≤ b`. On the two replicas `V ⊕ V` put `Ψ = Ω ⊗ Ω` and
`Φ = F_R Ψ`, where `F_R` exchanges the replicas on `R`. With the doubled Hamiltonian
`K = H ⊗ 1 + 1 ⊗ H`, there are a contraction `W` on the two copies of the buffer
`Q = (R ∪ C)ᶜ` and a real `z ≥ exp (-2 b)` such that, for every `L ≥ 1` and
`B = 1 + b + log L`, the truncated Gaussian integral `M` of variance `A B` and cutoff `T₀ B`
between the generators `F_R K F_R*` and `K`, applied to the placement of `W` on `Q ⊔ Q`, has
both residuals `‖M Ψ - z Φ‖` and `‖M* Φ - z Ψ‖` at most `3 exp (-10 b) L^(-r)`. The constants
are `A = 2 (30 + r) / Δ²` and `T₀ = 2 (30 + r) / Δ`. No gap of a restricted Hamiltonian, rank
bound or bound on purifying dimensions is assumed, and nothing depends on a geometry of the
sites.

The statement is that of the source in the coordinates of the two replicas `V ⊕ V`; the proof
transports `GaussianFilter.physicalBuffer_filter_of_le` from the coordinates of the two
regions and the buffer.

Moved from TNLean, `TNLean/Lattice/RegionalReset.lean` at commit `e41c3b63`
(`regional_physicalBuffer_filter`), restated on the sites `V ⊕ V` with the operator of the
exchange of replicas and the placement of the buffer operator.

## Main definitions

* `GaussianFilter.resetVariance`, `GaussianFilter.resetCutoff` — the Gaussian constants.

## Main results

* `GaussianFilter.regional_physicalBuffer_filter` — the two-sided Gaussian filter.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 355–452, equations
  `eq:info-split-overlap`, `eq:info-reset-overlap` and `eq:info-gaussian-two-sided`, with the
  constants at lines 443–450.
-/

open Matrix ManyBody
open scoped Kronecker ComplexOrder Matrix.Norms.L2Operator

namespace GaussianFilter

/-- The variance coefficient `A = 2 (30 + r) / Δ²` of the Gaussian filter of the information
reset; it meets `30 + r ≤ A Δ² / 2` with equality. Polynomial PEPS approximation,
`02-information.tex`, lines 426–427 and 443–444. -/
noncomputable def resetVariance (Δ r : ℝ) : ℝ := 2 * (30 + r) / Δ ^ 2

/-- The cutoff coefficient `T₀ = 2 (30 + r) / Δ` of the Gaussian filter of the information
reset; it meets `30 + r ≤ T₀² / (2 A)` with equality. Polynomial PEPS approximation,
`02-information.tex`, lines 443–450. -/
noncomputable def resetCutoff (Δ r : ℝ) : ℝ := 2 * (30 + r) / Δ

private theorem resetCutoff_nonneg {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 ≤ resetCutoff Δ r := by
  unfold resetCutoff
  positivity

private theorem le_resetVariance_mul_sq_div_two {Δ r : ℝ} (hΔ : Δ ≠ 0) :
    30 + r ≤ resetVariance Δ r * Δ ^ 2 / 2 := by
  unfold resetVariance
  field_simp
  rfl

private theorem le_resetCutoff_sq_div {Δ r : ℝ} (hΔ : Δ ≠ 0) (hr : 0 ≤ r) :
    30 + r ≤ resetCutoff Δ r ^ 2 / (2 * resetVariance Δ r) := by
  have h30 : (30 + r) ≠ 0 := by positivity
  unfold resetCutoff resetVariance
  field_simp
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The coordinates of two regions and the buffer on two replicas -/

section Coordinates

variable (R C : Finset V) (hRC : Disjoint R C)

/-- The coordinates of two regions and the buffer of one replica. -/
private noncomputable abbrev splitCoords :=
  ManyBody.splitTwoRegionsEquiv (fun _ : V ↦ α) R C hRC

/-- The coordinates `(R × C)² × Q²` of the two replicas, in the order of the physical-buffer
filter. -/
private noncomputable def replicaCoords :
    ((Fin (Fintype.card (ManyBody.RegionConfig (fun _ : V ↦ α) R)) ×
        Fin (Fintype.card (ManyBody.RegionConfig (fun _ : V ↦ α) C))) ×
      (Fin (Fintype.card (ManyBody.RegionConfig (fun _ : V ↦ α) R)) ×
        Fin (Fintype.card (ManyBody.RegionConfig (fun _ : V ↦ α) C)))) ×
      (ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C) × ManyBody.ComplConfig (fun _ : V ↦ α)
          (R ∪ C)) ≃
      Config (fun _ : V ⊕ V ↦ α) :=
  (((splitCoords R C hRC).prodCongr (splitCoords R C hRC)).trans
    (Equiv.doubledRegroup _ _)).symm.trans (Equiv.sumArrowEquivProdArrow V V α).symm

omit [Fintype V] [DecidableEq α] in
private theorem replicaCoords_symm_apply (x : Config fun _ : V ⊕ V ↦ α) :
    (replicaCoords (α := α) R C hRC).symm x =
      (((Fintype.equivFin (ManyBody.RegionConfig (fun _ : V ↦ α) R) (fun v ↦ x (.inl v)),
            Fintype.equivFin (ManyBody.RegionConfig (fun _ : V ↦ α) C) (fun v ↦ x (.inl v))),
          (Fintype.equivFin (ManyBody.RegionConfig (fun _ : V ↦ α) R) (fun v ↦ x (.inr v)),
            Fintype.equivFin (ManyBody.RegionConfig (fun _ : V ↦ α) C) (fun v ↦ x (.inr v)))),
        ((fun v ↦ x (.inl v) : ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C)),
          (fun v ↦ x (.inr v) : ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C)))) :=
  rfl

/-- In these coordinates, the exchange of replicas on `R` is the partial swap of the `R`
registers, tensored with the identity on the two buffers. -/
private theorem reindex_replicaCoords_partialSwap :
    reindex (replicaCoords (α := α) R C hRC) (replicaCoords R C hRC)
        (partialSwap (Fin (Fintype.card (ManyBody.RegionConfig (fun _ : V ↦ α) R)))
          (Fin (Fintype.card (ManyBody.RegionConfig (fun _ : V ↦ α) C))) ⊗ₖ
          (1 : Matrix (ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C) ×
          ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C))
              (ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C) ×
          ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C)) ℂ)) =
      sitePermOp (replicaSwap R) := by
  set G := replicaCoords (α := α) R C hRC
  set π := replicaSwap R
  have hC (v : V) (hv : v ∈ C) : v ∉ R := fun h ↦ Finset.disjoint_left.mp hRC h hv
  have hQ (v : V) (hv : v ∉ R ∪ C) : v ∉ R := fun h ↦ hv (Finset.mem_union_left C h)
  have hswap (x : Config fun _ : V ⊕ V ↦ α) :
      G.symm (x ∘ π) = (Equiv.partialSwap _ _ (G.symm x).1, (G.symm x).2) := by
    rw [replicaCoords_symm_apply, replicaCoords_symm_apply]
    have hl (v : V) (hv : v ∉ R) : (x ∘ π) (.inl v) = x (.inl v) := by
      change x (π (.inl v)) = _
      rw [replicaSwap_inl_of_notMem hv]
    have hr (v : V) (hv : v ∉ R) : (x ∘ π) (.inr v) = x (.inr v) := by
      change x (π (.inr v)) = _
      rw [replicaSwap_inr_of_notMem hv]
    have hlR (v : V) (hv : v ∈ R) : (x ∘ π) (.inl v) = x (.inr v) := by
      change x (π (.inl v)) = _
      rw [replicaSwap_inl_of_mem hv]
    have hrR (v : V) (hv : v ∈ R) : (x ∘ π) (.inr v) = x (.inl v) := by
      change x (π (.inr v)) = _
      rw [replicaSwap_inr_of_mem hv]
    simp only [Equiv.partialSwap_apply]
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) (Prod.ext ?_ ?_)
    · exact congrArg (Fintype.equivFin _) (funext fun v : R ↦ hlR v v.2)
    · exact congrArg (Fintype.equivFin _) (funext fun v : C ↦ hl v (hC v v.2))
    · exact congrArg (Fintype.equivFin _) (funext fun v : R ↦ hrR v v.2)
    · exact congrArg (Fintype.equivFin _) (funext fun v : C ↦ hr v (hC v v.2))
    · exact funext fun v ↦ hl v (hQ v v.2)
    · exact funext fun v ↦ hr v (hQ v v.2)
  ext x y
  have hiff : y = x ∘ π ↔ (G.symm y).1 = Equiv.partialSwap _ _ (G.symm x).1 ∧
      (G.symm x).2 = (G.symm y).2 := by
    rw [← G.symm.apply_eq_iff_eq, hswap, Prod.ext_iff]
    exact and_congr Iff.rfl eq_comm
  rw [reindex_apply, submatrix_apply, kroneckerMap_apply, partialSwap_apply, one_apply,
    sitePermOp_apply, ite_zero_mul_ite_zero, mul_one]
  exact if_congr hiff.symm rfl rfl

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
private theorem reindex_prodCongr_doubledHamiltonian {m n : Type*} [DecidableEq m]
    [DecidableEq n] (e : m ≃ n) (H : Matrix m m ℂ) :
    reindex (e.prodCongr e) (e.prodCongr e) (doubledHamiltonian H) =
      doubledHamiltonian (reindex e e H) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [doubledHamiltonian, kroneckerMap_apply, one_apply, e.symm.injective.eq_iff]

/-- In these coordinates, the doubled Hamiltonian is the doubled Hamiltonian of the
regional coordinates of one replica. -/
private theorem reindex_replicaCoords_doubledHamiltonian
    (H : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) :
    reindex (replicaCoords (α := α) R C hRC) (replicaCoords R C hRC)
        (reindex (Equiv.doubledRegroup _ _) (Equiv.doubledRegroup _ _)
          (doubledHamiltonian (reindex (splitCoords R C hRC) (splitCoords R C hRC) H))) =
      reindex (Equiv.sumArrowEquivProdArrow V V α).symm
        (Equiv.sumArrowEquivProdArrow V V α).symm (doubledHamiltonian H) := by
  rw [← reindex_prodCongr_doubledHamiltonian]
  ext x y
  simp [replicaCoords, Prod.map]

omit [Fintype V] [DecidableEq α] in
/-- In these coordinates, the doubled vector is `Ω ⊗ Ω`. -/
private theorem doubledRegroup_comp_replicaCoords_symm
    (Ω : EuclideanSpace ℂ (Config fun _ : V ↦ α)) :
    doubledRegroup (ManyBody.splitTwoRegionsState (fun _ : V ↦ α) Ω R C hRC) ∘
        (replicaCoords (α := α) R C hRC).symm =
      WithLp.ofLp (ManyBody.sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω) := by
  funext x
  simp [replicaCoords, doubledRegroup, ManyBody.splitTwoRegionsState, ManyBody.sumSitesProduct,
    Equiv.doubledRegroup, Equiv.bipartiteRegroup]
  rfl

/-- Pairing the configurations of the two buffers. -/
private def bufferPairEquiv :
    ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C) × ManyBody.ComplConfig (fun _ : V ↦ α)
        (R ∪ C) ≃
      RegionConfig (fun _ : V ⊕ V ↦ α) (((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ) :=
  ((ManyBody.complementEquiv _ (R ∪ C)).prodCongr (ManyBody.complementEquiv _ (R ∪ C))).trans
    ((replicaPairRegionEquiv (R ∪ C)ᶜ).trans (Equiv.arrowProdEquivProdArrow _ _ _)).symm

omit [DecidableEq α] in
private theorem agree_iff_replicaCoords (x y : Config fun _ : V ⊕ V ↦ α) :
    ((replicaCoords (α := α) R C hRC).symm x).1 = ((replicaCoords R C hRC).symm y).1 ↔
      ∀ w ∉ ((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ, x w = y w := by
  rw [replicaCoords_symm_apply, replicaCoords_symm_apply]
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, funext_iff, Subtype.forall]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ (v | v) hw
    · have hv : v ∈ R ∪ C := by simpa [or_iff_not_imp_left] using hw
      rcases Finset.mem_union.mp hv with hv | hv
      · exact h₁ v hv
      · exact h₂ v hv
    · have hv : v ∈ R ∪ C := by simpa [or_iff_not_imp_left] using hw
      rcases Finset.mem_union.mp hv with hv | hv
      · exact h₃ v hv
      · exact h₄ v hv
  · intro h
    exact ⟨⟨fun v hv ↦ h (.inl v) (by simp [hv]), fun v hv ↦ h (.inl v) (by simp [hv])⟩,
      fun v hv ↦ h (.inr v) (by simp [hv]), fun v hv ↦ h (.inr v) (by simp [hv])⟩

/-- In these coordinates, a buffer operator `1 ⊗ W` is the placement of `W` on the two copies
of the buffer. -/
private theorem reindex_replicaCoords_one_kronecker
    (W : Matrix
        (ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C) × ManyBody.ComplConfig (fun _ : V ↦ α)
        (R ∪ C))
      (ManyBody.ComplConfig (fun _ : V ↦ α) (R ∪ C) × ManyBody.ComplConfig (fun _ : V ↦ α)
          (R ∪ C)) ℂ) :
    reindex (replicaCoords (α := α) R C hRC) (replicaCoords R C hRC)
        ((1 : Matrix _ _ ℂ) ⊗ₖ W) =
      place (((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ)
        (reindex (bufferPairEquiv R C) (bufferPairEquiv R C) W) := by
  ext x y
  rw [reindex_apply, submatrix_apply, kroneckerMap_apply, one_apply, place_apply,
    reindex_apply, submatrix_apply]
  by_cases h : ∀ w ∉ ((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ, x w = y w
  · rw [ite_eq_left ((agree_iff_replicaCoords R C hRC x y).mpr h), ite_eq_left h, one_mul]
    rfl
  · rw [ite_eq_right (mt (agree_iff_replicaCoords R C hRC x y).mp h), ite_eq_right h, zero_mul]

end Coordinates

private theorem norm_toLp_comp_symm {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n)
    (f : m → ℂ) : ‖(WithLp.toLp 2 (f ∘ e.symm) : EuclideanSpace ℂ _)‖ =
      ‖(WithLp.toLp 2 f : EuclideanSpace ℂ m)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact e.symm.sum_comp (fun k ↦ ‖f k‖ ^ 2)

/-- **The two-sided Gaussian filter of the information reset.** Let `H` be Hermitian and gapped
at `E₀` with gap `Δ > 0`, with ground space the line through the unit vector `Ω`, let `r ≥ 0`,
and let `R, C` be disjoint regions with `I_Ω(R : C) ≤ b`. On the two replicas put
`Ψ = Ω ⊗ Ω`, the exchange `F = F_R` and the doubled Hamiltonian `K`. Then a Hermitian
contraction `W` on the two copies of the buffer `Q = (R ∪ C)ᶜ` and a real `z ≥ exp (-2 b)` are
chosen once, and for every `L ≥ 1`, with `B = 1 + b + log L`, the Gaussian integral `M` of
variance `A B` truncated at `T₀ B`, for `A = resetVariance Δ r` and `T₀ = resetCutoff Δ r`,
between the generators `F K F*` and `K` applied to the placement of `W` on `Q ⊔ Q`, satisfies
`‖M‖ ≤ 1` and has both residuals `‖M Ψ - z F Ψ‖` and `‖M* F Ψ - z Ψ‖` at most
`3 exp (-10 b) L^(-r)`. Polynomial PEPS approximation, `02-information.tex`, lines 355–452,
equations `eq:info-split-overlap`, `eq:info-reset-overlap` and `eq:info-gaussian-two-sided`. -/
theorem regional_physicalBuffer_filter {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r)
    {H : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ} (hH : H.IsHermitian)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Config fun _ : V ↦ α)} (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped H E₀ Δ) (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω})
    {R C : Finset V} (hRC : Disjoint R C) {b : ℝ}
    (hI : ManyBody.regionMutualInformation Ω R C ≤ b) :
    let K := reindex (Equiv.sumArrowEquivProdArrow V V α).symm
      (Equiv.sumArrowEquivProdArrow V V α).symm (doubledHamiltonian H)
    let F := sitePermOp (α := α) (replicaSwap R)
    let Ψ := ManyBody.sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω
    ∃ (W : Matrix (RegionConfig (fun _ : V ⊕ V ↦ α) (((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ))
        (RegionConfig (fun _ : V ⊕ V ↦ α) (((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ)) ℂ) (z : ℝ),
      W.IsHermitian ∧ ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧
      ∀ L : ℝ, 1 ≤ L →
        let B := 1 + b + Real.log L
        let M := gaussianIntertwinerTruncated (Real.toNNReal (resetVariance Δ r * B))
          (resetCutoff Δ r * B) (F * K * Fᴴ) K (place (((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ) W)
        ‖M‖ ≤ 1 ∧
          ‖toEuclideanLin M Ψ - (z : ℂ) • toEuclideanLin F Ψ‖ ≤
            3 * Real.exp (-10 * b) * L ^ (-r) ∧
          ‖toEuclideanLin Mᴴ (toEuclideanLin F Ψ) - (z : ℂ) • Ψ‖ ≤
            3 * Real.exp (-10 * b) * L ^ (-r) := by
  intro K F Ψ
  set s := splitCoords (α := α) R C hRC
  set G := replicaCoords (α := α) R C hRC
  have hb : 0 ≤ b := (ManyBody.regionMutualInformation_nonneg _ Ω hΩ R C hRC).trans hI
  have heigen := mulVec_eq_of_groundSpace_eq_span hspan
  have hgap := hgs.posSemidef_sub_smul_one hH hΩ hspan
  let Ωs := ManyBody.splitTwoRegionsState (fun _ : V ↦ α) Ω R C hRC
  have hΩsv : Ωs = WithLp.ofLp Ω ∘ s.symm := rfl
  have hunit : star Ωs ⬝ᵥ Ωs = 1 := ManyBody.splitTwoRegionsState_unit _ Ω hΩ R C hRC
  have heigs : reindex s s H *ᵥ Ωs = (E₀ : ℂ) • Ωs := by
    rw [hΩsv, Matrix.reindex_mulVec, heigen]
    rfl
  have hgaps : (reindex s s H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec Ωs (star Ωs))).PosSemidef := by
    convert hgap.submatrix s.symm using 1
    ext x y
    simp [hΩsv, vecMulVec_apply, one_apply, s.symm.injective.eq_iff]
  have hbound : quantumRelativeEntropy (partialTraceRight (vecMulVec Ωs (star Ωs)))
      (partialTraceRight (partialTraceRight (vecMulVec Ωs (star Ωs))) ⊗ₖ
        partialTraceLeft (partialTraceRight (vecMulVec Ωs (star Ωs)))) ≤ b := by
    rw [ManyBody.partialTraceRight_splitTwoRegionsState,
      quantumRelativeEntropy_product_marginals (ManyBody.jointMatrix_posSemidef _ Ω R C hRC)]
    rw [ManyBody.regionMutualInformation_eq_matrix _ Ω R C hRC] at hI
    exact hI
  have hfilter := physicalBuffer_filter_of_le hΔ hr (resetCutoff_nonneg hΔ hr)
    (le_resetVariance_mul_sq_div_two hΔ.ne') (le_resetCutoff_sq_div hΔ.ne' hr) _ _ _
    (reindex s s H) Ωs E₀ b hunit heigs hgaps hb hbound
  obtain ⟨W, z, hWherm, hW, hz, -, hfil⟩ := hfilter
  have hK := reindex_replicaCoords_doubledHamiltonian (α := α) R C hRC H
  have hS := reindex_replicaCoords_partialSwap (α := α) R C hRC
  have hV := reindex_replicaCoords_one_kronecker (α := α) R C hRC W
  have hψ := doubledRegroup_comp_replicaCoords_symm (α := α) R C hRC Ω
  have hφ : physicalLeftSwap (doubledRegroup Ωs) ∘ G.symm = F *ᵥ WithLp.ofLp Ψ := by
    rw [physicalLeftSwap_eq_mulVec, ← hψ, ← Matrix.reindex_mulVec]
    exact congrArg (· *ᵥ _) hS
  refine ⟨reindex (bufferPairEquiv R C) (bufferPairEquiv R C) W, z,
    hWherm.submatrix _, ?_, hz, fun L hL ↦ ?_⟩
  · have := hWherm
    rw [Matrix.l2_opNorm_reindex_equiv]
    exact hW
  obtain ⟨-, -, -, hM, hfwd, hrev⟩ := hfil L hL
  have hmul (X Y : Matrix ((_ × _) × (_ × _)) ((_ × _) × (_ × _)) ℂ) :
      reindex G G (X * Y) = reindex G G X * reindex G G Y := by
    simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℂ ℂ G) X Y
  set B := 1 + b + Real.log L
  set M₀ := gaussianIntertwinerTruncated (Real.toNNReal (resetVariance Δ r * B))
    (resetCutoff Δ r * B)
    ((partialSwap _ _ ⊗ₖ (1 : Matrix _ _ ℂ)) *
      reindex (Equiv.doubledRegroup _ _) (Equiv.doubledRegroup _ _)
        (doubledHamiltonian (reindex s s H)) * (partialSwap _ _ ⊗ₖ (1 : Matrix _ _ ℂ))ᴴ)
    (reindex (Equiv.doubledRegroup _ _) (Equiv.doubledRegroup _ _)
      (doubledHamiltonian (reindex s s H))) ((1 : Matrix _ _ ℂ) ⊗ₖ W)
  have hM₀ : reindex G G M₀ = gaussianIntertwinerTruncated
      (Real.toNNReal (resetVariance Δ r * B)) (resetCutoff Δ r * B) (F * K * Fᴴ) K
      (place (((R ∪ C)ᶜ).disjSum (R ∪ C)ᶜ)
        (reindex (bufferPairEquiv R C) (bufferPairEquiv R C) W)) := by
    rw [reindex_gaussianIntertwinerTruncated, hmul, hmul, ← conjTranspose_reindex, hS, hK, hV]
  have hvec (A : Matrix ((_ × _) × (_ × _)) ((_ × _) × (_ × _)) ℂ) (u : _ → ℂ) :
      reindex G G A *ᵥ (u ∘ G.symm) = (A *ᵥ u) ∘ G.symm := by
    rw [Matrix.reindex_mulVec]
  have hΨ : WithLp.ofLp Ψ = doubledRegroup Ωs ∘ G.symm := hψ.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hM₀, Matrix.l2_opNorm_reindex_equiv]
    exact hM
  · rw [← hM₀]
    change ‖WithLp.toLp 2 (reindex G G M₀ *ᵥ WithLp.ofLp Ψ) -
      (z : ℂ) • WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)‖ ≤ _
    rw [← hφ, hΨ, hvec, ← WithLp.toLp_smul, ← WithLp.toLp_sub]
    have hsc : (z : ℂ) • (physicalLeftSwap (doubledRegroup Ωs) ∘ G.symm) =
        ((z : ℂ) • physicalLeftSwap (doubledRegroup Ωs)) ∘ G.symm := rfl
    rw [hsc, ← Pi.sub_comp, norm_toLp_comp_symm, WithLp.toLp_sub, WithLp.toLp_smul]
    exact hfwd
  · rw [← hM₀, conjTranspose_reindex]
    change ‖WithLp.toLp 2 (reindex G G M₀ᴴ *ᵥ (F *ᵥ WithLp.ofLp Ψ)) -
      (z : ℂ) • WithLp.toLp 2 (WithLp.ofLp Ψ)‖ ≤ _
    rw [← hφ, hΨ, hvec, ← WithLp.toLp_smul, ← WithLp.toLp_sub]
    have hsc : (z : ℂ) • (doubledRegroup Ωs ∘ G.symm) =
        ((z : ℂ) • doubledRegroup Ωs) ∘ G.symm := rfl
    rw [hsc, ← Pi.sub_comp, norm_toLp_comp_symm, WithLp.toLp_sub, WithLp.toLp_smul]
    exact hrev

end GaussianFilter
