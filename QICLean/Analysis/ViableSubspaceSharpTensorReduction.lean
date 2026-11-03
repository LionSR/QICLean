/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSpectralProjector
import QICLean.Analysis.ViableSubspaceSharpErrorReduction

/-!
# Sharp viability reduction by a finite tensor family

The normalized projection estimate applies to the actual retained-factor
family in a tensor decomposition. The low target is invariant and the
filter does not decrease norms there; it need not act as the identity on
that target. The same statement allows nested low-energy targets without
assuming a spectral gap between them.

These are supporting estimates for ALVV, arXiv:1602.08828v2,
Lemma `l:er`, lines 597–622, and Theorem `t:aisgapless`, lines 1037–1041.
The physical construction and the trimming analysis remain separate.
-/

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {𝕜 M R : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]

/-- A finite tensor decomposition yields sharp normalized viability for a
nested lower target. Only minimum gain one on the lower target is needed;
there is no identity-on-band hypothesis. This refines the projection
argument in ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 606–622,
and Theorem `t:aisgapless`, lines 1037–1041. -/
theorem IsViable.map_of_nested_tensor_decomposition_sharp
    {ι : Type*} [Fintype ι] {δ Δ : ℝ}
    {S : Submodule 𝕜 M} {T Tplus : Submodule 𝕜 (M ⊗[𝕜] R)}
    {K : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R}
    (hT : T ≤ Tplus) (hS : IsViable δ S Tplus)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i))
    (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hΔ : 0 ≤ Δ)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ q ∈ Tplusᗮ, K q ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ q ∈ Tplusᗮ, ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2) :
    Module.finrank 𝕜 ↥(⨆ i, S.map (A i : M →ₗ[𝕜] M)) ≤
        Fintype.card ι * Module.finrank 𝕜 S ∧
      IsViable (Δ * δ / (1 - δ + Δ * δ))
        (⨆ i, S.map (A i : M →ₗ[𝕜] M)) T := by
  refine ⟨finrank_iSup_map_le_card_mul S (fun i ↦ (A i).toLinearMap), ?_⟩
  exact (hS.map_of_nested_contract_sharp K hT hδ0 hδ hΔ hKT hKTo hlow hhigh).mono
    (map_tensorProd_top_le_iSup_map S A B hdec)

/-- Sharp viability reduction for one target and the actual retained-factor
family. The low-band operator need not be constant. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 606–622. -/
theorem IsViable.map_of_tensor_decomposition_sharp
    {ι : Type*} [Fintype ι] {δ Δ : ℝ}
    {S : Submodule 𝕜 M} {T : Submodule 𝕜 (M ⊗[𝕜] R)}
    {K : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R}
    (hS : IsViable δ S T)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i))
    (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hΔ : 0 ≤ Δ)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ q ∈ Tᗮ, K q ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ q ∈ Tᗮ, ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2) :
    Module.finrank 𝕜 ↥(⨆ i, S.map (A i : M →ₗ[𝕜] M)) ≤
        Fintype.card ι * Module.finrank 𝕜 S ∧
      IsViable (Δ * δ / (1 - δ + Δ * δ))
        (⨆ i, S.map (A i : M →ₗ[𝕜] M)) T := by
  exact hS.map_of_nested_tensor_decomposition_sharp le_rfl A B hdec
    hδ0 hδ hΔ hKT hKTo hlow hhigh

end Submodule
