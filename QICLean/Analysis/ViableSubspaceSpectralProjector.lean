/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceErrorReduction
import QICLean.Analysis.ViableSubspaceTensor

/-!
# Error reduction of a viable subspace by a spectral projector

Arad, Landau, Vazirani and Vidick, *Rigorous RG algorithms and area laws for low energy
eigenstates in 1D* (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`), improve a viable set
`S ⊆ H_M` for the low-energy space `T` of a Hamiltonian `H` on `H_L ⊗ H_M ⊗ H_R` by applying a
spectral approximate ground state projection `K = ∑_{i ≤ D²} L_i ⊗ A_i ⊗ R_i`
(Definition `def:spectral-AGSP`, lines 570–581). Lemma `l:er` (lines 597–622) states that
`span {A_i S}` has dimension at most `D² dim S` and is `Δ / (1 - δ) ^ 2`-viable for `T`.

`H` and `K` have the same eigenvectors, which we express by an orthonormal basis `b` of common
eigenvectors, with eigenvalues `h j` of `H` and `k j` of `K`. The low-energy space
`T = H_{[ε₀, η₀]}` is the span of the `b j` with `h j ≤ η₀`.

**Local fix (closed spectral conditions; the printed lemma is false at `η₀`).** The printed
definition asks that eigenvalues of `H` below `η₀` give eigenvalues of `K` at least `1`, and
eigenvalues above `η₁` give eigenvalues below `√Δ`. The lemma's target `T` contains the
eigenvalue `η₀` itself, where the printed lemma fails even for positive definite `K`, and its
complement may contain `η₁`. The proof needs the closed conditions `h j ≤ η₀ → 1 ≤ k j` and
`η₁ ≤ h j → k j ^ 2 ≤ Δ`, which `IsSpectralProjector` states. Definition `d:vs` allows
`δ = 1`, where `Δ / (1 - δ) ^ 2` is undefined; by convention the lemma assumes `δ < 1`, as the
proof does through Lemma `l:2`. Positivity of `K` is not used and not assumed. Documented in
`docs/paper-gaps/alvv16_spectral_projector_boundary.tex`.

## Main statements

* `Submodule.IsSpectralProjector`: Definition `def:spectral-AGSP` with closed conditions.
* `Submodule.IsViable.spectralProjector`: Lemma `l:er`.
-/

open scoped TensorProduct InnerProductSpace
open TensorProduct Module

namespace Submodule

section General

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
theorem tmul_mem_tensorProd {S : Submodule 𝕜 E} {S' : Submodule 𝕜 F} {x : E} {y : F}
    (hx : x ∈ S) (hy : y ∈ S') : x ⊗ₜ[𝕜] y ∈ S.tensorProd S' :=
  ⟨⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩, TensorProduct.map_tmul _ _ _ _⟩

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- `S ⊗ S'` lies in `N` exactly when every `x ⊗ y` with `x ∈ S` and `y ∈ S'` does. -/
theorem tensorProd_le_iff {S : Submodule 𝕜 E} {S' : Submodule 𝕜 F}
    {N : Submodule 𝕜 (E ⊗[𝕜] F)} :
    S.tensorProd S' ≤ N ↔ ∀ x ∈ S, ∀ y ∈ S', x ⊗ₜ[𝕜] y ∈ N := by
  refine ⟨fun h x hx y hy => h (tmul_mem_tensorProd hx hy), fun h => ?_⟩
  rintro _ ⟨z, rfl⟩
  induction z with
  | tmul x y =>
    rw [TensorProduct.map_tmul]
    exact h x x.2 y y.2
  | add z z' hz hz' =>
    rw [map_add]
    exact N.add_mem hz hz'

omit [FiniteDimensional 𝕜 E] in
/-- The dimension of a finite supremum of subspaces is at most the sum of the dimensions. -/
theorem finrank_iSup_le_sum {ι : Type*} [Fintype ι] (f : ι → Submodule 𝕜 E)
    [∀ i, FiniteDimensional 𝕜 (f i)] :
    finrank 𝕜 ↥(⨆ i, f i) ≤ ∑ i, finrank 𝕜 (f i) := by
  classical
  rw [← Finset.sup_univ_eq_iSup]
  generalize (Finset.univ : Finset ι) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    have : FiniteDimensional 𝕜 ↥(s.sup f) := by
      rw [Finset.sup_eq_iSup]
      infer_instance
    exact (finrank_add_le_finrank_add_finrank _ _).trans (by gcongr)

end General

variable {𝕜 E L M R : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [FiniteDimensional 𝕜 L]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
  {n : Type*} [Fintype n]

/-- **Definition `def:spectral-AGSP` (spectral conditions).** `K` is a spectral approximate ground
state projection for `(H, η₀, η₁)` with parameter `Δ` relative to an orthonormal basis `b` of
common eigenvectors: `H b_j = h_j b_j`, `K b_j = k_j b_j`, eigenvalues `h_j ≤ η₀` give
`k_j ≥ 1`, and eigenvalues `h_j ≥ η₁` give `k_j ^ 2 ≤ Δ`. Arad, Landau, Vazirani and
Vidick, arXiv:1602.08828v2, Definition `def:spectral-AGSP` (lines 570–581), with the closed
conditions of the module docstring. The tensor decomposition of `K` is a separate hypothesis. -/
structure IsSpectralProjector (K H : E →L[𝕜] E) (b : OrthonormalBasis n 𝕜 E) (h k : n → ℝ)
    (η₀ η₁ Δ : ℝ) : Prop where
  apply_H : ∀ j, H (b j) = (h j : 𝕜) • b j
  apply_K : ∀ j, K (b j) = (k j : 𝕜) • b j
  one_le : ∀ j, h j ≤ η₀ → 1 ≤ k j
  sq_le : ∀ j, η₁ ≤ h j → k j ^ 2 ≤ Δ

omit [FiniteDimensional 𝕜 E] in
/-- On the low-energy space `T = span {b_j : h_j ≤ η₀}`, a spectral projector satisfies the
hypotheses of `IsCloseTo.map_of_contract` when `H` has no eigenvalue in `(η₀, η₁)`. -/
theorem IsSpectralProjector.contract {K H : E →L[𝕜] E} {b : OrthonormalBasis n 𝕜 E}
    {h k : n → ℝ} {η₀ η₁ Δ : ℝ} (hK : IsSpectralProjector K H b h k η₀ η₁ Δ)
    (hgap : ∀ j, h j ≤ η₀ ∨ η₁ ≤ h j) :
    let T := span 𝕜 (b '' {j | h j ≤ η₀})
    (∀ t ∈ T, K t ∈ T) ∧ (∀ q ∈ Tᗮ, K q ∈ Tᗮ) ∧ (∀ t ∈ T, ‖t‖ ≤ ‖K t‖) ∧
      (∀ q ∈ Tᗮ, ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2) := by
  intro T
  have hrepr : ∀ x j, b.repr (K x) j = (k j : 𝕜) * b.repr x j := by
    intro x j
    conv_lhs => rw [← b.sum_repr x]
    rw [b.repr_apply_apply, map_sum]
    simp_rw [map_smul, hK.apply_K, smul_smul]
    rw [b.orthonormal.inner_right_fintype, mul_comm]
  have hnorm : ∀ x, ‖x‖ ^ 2 = ∑ j, ‖b.repr x j‖ ^ 2 := by
    intro x
    simp_rw [b.repr_apply_apply]
    exact (b.sum_sq_norm_inner_right x).symm
  have memT : ∀ x, x ∈ T ↔ ∀ j, ¬ h j ≤ η₀ → b.repr x j = 0 := by
    intro x
    have hT : T = span 𝕜 (b.toBasis '' {j | h j ≤ η₀}) := by
      rw [OrthonormalBasis.coe_toBasis]
    rw [hT, Basis.mem_span_image]
    simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
      OrthonormalBasis.coe_toBasis_repr_apply, Set.mem_ofPred_eq]
    exact ⟨fun h' j hj => by_contra fun hne => hj (h' j hne),
      fun h' j hne => by_contra fun hj => hne (h' j hj)⟩
  have memTo : ∀ x, x ∈ Tᗮ ↔ ∀ j, h j ≤ η₀ → b.repr x j = 0 := by
    intro x
    refine ⟨fun hx j hj => ?_, fun hx => ?_⟩
    · rw [b.repr_apply_apply]
      exact inner_right_of_mem_orthogonal
        (subset_span (Set.mem_image_of_mem b (show j ∈ {j | h j ≤ η₀} from hj))) hx
    · rw [mem_orthogonal]
      intro u hu
      rw [← b.sum_inner_mul_inner]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : h j ≤ η₀
      · rw [← b.repr_apply_apply, hx j hj, mul_zero]
      · rw [← inner_conj_symm, ← b.repr_apply_apply, (memT u).mp hu j hj, map_zero, zero_mul]
  have hnormK : ∀ x, ‖K x‖ ^ 2 = ∑ j, k j ^ 2 * ‖b.repr x j‖ ^ 2 := by
    intro x
    rw [hnorm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrepr, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  refine ⟨fun t ht => ?_, fun q hq => ?_, fun t ht => ?_, fun q hq => ?_⟩
  · rw [memT] at ht ⊢
    intro j hj
    rw [hrepr, ht j hj, mul_zero]
  · rw [memTo] at hq ⊢
    intro j hj
    rw [hrepr, hq j hj, mul_zero]
  · rw [memT] at ht
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hnormK, hnorm]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : h j ≤ η₀
    · have h1 := hK.one_le j hj
      have : 1 ≤ k j ^ 2 := one_le_pow₀ h1
      nlinarith [sq_nonneg ‖b.repr t j‖]
    · rw [ht j hj, norm_zero]
      simp
  · rw [memTo] at hq
    rw [hnormK, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : h j ≤ η₀
    · rw [hq j hj, norm_zero]
      simp
    · have := hK.sq_le j ((hgap j).resolve_left hj)
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- **Lemma `l:er` (error reduction by a spectral projector).** Let `K` be a spectral approximate
ground state projection for `(H, η₀, η₁)` with parameter `Δ`, decomposed as
`K = ∑_{i < D²} L_i ⊗ A_i ⊗ R_i`, let `H` have no eigenvalue in `(η₀, η₁)`, and let `S ⊆ H_M` be
`δ`-viable, `δ < 1`, for the low-energy space `T = span {b_j : h_j ≤ η₀}`. Then
`V = span {A_i S}` has dimension at most `D² dim S` and is `Δ / (1 - δ) ^ 2`-viable for `T`.
Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Lemma `l:er` (lines 597–622), with the
local fix of the module docstring. -/
theorem IsViable.spectralProjector {D : ℕ} {δ Δ η₀ η₁ : ℝ}
    {K H : (L ⊗[𝕜] M) ⊗[𝕜] R →L[𝕜] (L ⊗[𝕜] M) ⊗[𝕜] R}
    {b : OrthonormalBasis n 𝕜 ((L ⊗[𝕜] M) ⊗[𝕜] R)} {h k : n → ℝ}
    (hK : IsSpectralProjector K H b h k η₀ η₁ Δ)
    (Lop : Fin (D ^ 2) → L →L[𝕜] L) (A : Fin (D ^ 2) → M →L[𝕜] M) (Rop : Fin (D ^ 2) → R →L[𝕜] R)
    (hdec : K = ∑ i, mapL (mapL (Lop i) (A i)) (Rop i))
    (hgap : ∀ j, h j ≤ η₀ ∨ η₁ ≤ h j) {S : Submodule 𝕜 M}
    (hS : IsViable δ ((⊤ : Submodule 𝕜 L).tensorProd S) (span 𝕜 (b '' {j | h j ≤ η₀})))
    (hδ : δ < 1) (hΔ : 0 ≤ Δ) :
    finrank 𝕜 ↥(⨆ i, S.map (A i : M →ₗ[𝕜] M)) ≤ D ^ 2 * finrank 𝕜 S ∧
      IsViable (Δ / (1 - δ) ^ 2)
        ((⊤ : Submodule 𝕜 L).tensorProd (⨆ i, S.map (A i : M →ₗ[𝕜] M)))
        (span 𝕜 (b '' {j | h j ≤ η₀})) := by
  set V := ⨆ i, S.map (A i : M →ₗ[𝕜] M)
  refine ⟨?_, ?_⟩
  · refine (finrank_iSup_le_sum _).trans ?_
    calc ∑ i, finrank 𝕜 ↥(S.map (A i : M →ₗ[𝕜] M)) ≤ ∑ _i : Fin (D ^ 2), finrank 𝕜 S :=
          Finset.sum_le_sum fun i _ => finrank_map_le _ _
      _ = D ^ 2 * finrank 𝕜 S := by simp
  · obtain ⟨hKT, hKTo, hlow, hhigh⟩ := hK.contract hgap
    have hclose := IsCloseTo.map_of_contract K hS hδ hΔ hKT hKTo hlow hhigh
    refine hclose.mono ?_
    have hslice : (⊤ : Submodule 𝕜 L).tensorProd S ≤
        ⨅ y : R, ((((⊤ : Submodule 𝕜 L).tensorProd V).tensorProd (⊤ : Submodule 𝕜 R)).comap
          (K : (L ⊗[𝕜] M) ⊗[𝕜] R →ₗ[𝕜] (L ⊗[𝕜] M) ⊗[𝕜] R)).comap
          ((TensorProduct.mk 𝕜 (L ⊗[𝕜] M) R).flip y) := by
      rw [tensorProd_le_iff]
      intro l _ s hs
      simp only [mem_iInf, mem_comap]
      intro y
      rw [LinearMap.flip_apply, TensorProduct.mk_apply, ContinuousLinearMap.coe_coe, hdec,
        sum_apply]
      refine sum_mem fun i _ => ?_
      rw [mapL_tmul, mapL_tmul]
      exact tmul_mem_tensorProd (tmul_mem_tensorProd mem_top
        (mem_iSup_of_mem i (mem_map_of_mem hs))) mem_top
    rw [map_le_iff_le_comap, tensorProd_le_iff]
    intro x hx y _
    have := (mem_iInf _).mp (hslice hx) y
    simpa using this

end Submodule
