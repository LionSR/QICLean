/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Viable subspaces of a tensor product

Arad, Landau, Vazirani and Vidick, *Rigorous RG algorithms and area laws for low energy
eigenstates in 1D* (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Section `s:vs`), call a
subspace `S ⊆ H_A` `δ`-viable for `T ⊆ H_A ⊗ H_B` when `P_T P_{S ⊗ H_B} P_T ≥ (1 - δ) P_T`
(Definition `d:vs`, lines 433–440), that is, when `S ⊗ H_B` is `δ`-close to `T`.

The tensor product `S ⊗ S'` of subspaces is the range of the tensor product of the inclusions,
and its orthogonal projection is `P_S ⊗ P_{S'}` (`starProjection_tensorProd`). Viable sets on
disjoint subsystems tensor (Lemma `l:t`, lines 500–523): if `S₁ ⊆ H_{A₁}` is `δ₁`-viable and
`S₂ ⊆ H_{A₂}` is `δ₂`-viable for `T ⊆ H_{A₁} ⊗ H_{A₂} ⊗ H_B`, then `S₁ ⊗ S₂` is
`(δ₁ + δ₂)`-viable. Here the viability of `S₁` is that of `S₁ ⊗ H_{A₂}` in `H_{A₁} ⊗ H_{A₂}`,
which is the same subspace `S₁ ⊗ H_{A₂} ⊗ H_B` of the three-fold product.

## Main statements

* `Submodule.tensorProd`, `Submodule.starProjection_tensorProd`: the tensor product of subspaces
  and its projection.
* `Submodule.IsViable`: Definition `d:vs`.
* `Submodule.IsViable.tensorProd`: Lemma `l:t`.
-/

open scoped TensorProduct InnerProductSpace
open TensorProduct

namespace Submodule

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- The tensor product `S ⊗ S'` of subspaces `S ⊆ E` and `S' ⊆ F`, as a subspace of `E ⊗ F`:
the range of the tensor product of the two inclusions. -/
def tensorProd (S : Submodule 𝕜 E) (S' : Submodule 𝕜 F) : Submodule 𝕜 (E ⊗[𝕜] F) :=
  LinearMap.range (TensorProduct.map S.subtype S'.subtype)

/-- The orthogonal projection onto `S ⊗ S'` is `P_S ⊗ P_{S'}`. -/
theorem starProjection_tensorProd (S : Submodule 𝕜 E) (S' : Submodule 𝕜 F) :
    (S.tensorProd S').starProjection = mapL S.starProjection S'.starProjection := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have : CompleteSpace (E ⊗[𝕜] F) := FiniteDimensional.complete 𝕜 _
  set p := mapL S.starProjection S'.starProjection with hp_def
  have hp : IsStarProjection p := by
    refine ⟨?_, ?_⟩
    · change p * p = p
      rw [hp_def, ← mapL_mul, S.isIdempotentElem_starProjection.eq,
        S'.isIdempotentElem_starProjection.eq]
    · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, hp_def, adjoint_mapL,
        ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
        (isSelfAdjoint_starProjection S).star_eq, (isSelfAdjoint_starProjection S').star_eq]
  obtain ⟨hw, hp'⟩ := isStarProjection_iff_eq_starProjection_range.mp hp
  have hr : p.range = S.tensorProd S' := by
    have hfac : p = mapL S.subtypeL S'.subtypeL ∘L
        mapL S.orthogonalProjectionOnto S'.orthogonalProjectionOnto := by
      rw [← mapL_comp]
      rfl
    rw [hfac]
    change LinearMap.range ((mapL S.subtypeL S'.subtypeL : S ⊗[𝕜] S' →ₗ[𝕜] E ⊗[𝕜] F) ∘ₗ
      (mapL S.orthogonalProjectionOnto S'.orthogonalProjectionOnto :
        E ⊗[𝕜] F →ₗ[𝕜] S ⊗[𝕜] S')) = _
    rw [toLinearMap_mapL, toLinearMap_mapL, LinearMap.range_comp_of_range_eq_top,
      toLinearMap_subtypeL, toLinearMap_subtypeL]
    · rfl
    · have h₁ : Function.Surjective (S.orthogonalProjectionOnto : E →ₗ[𝕜] S) :=
        fun x => ⟨x, S.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
      have h₂ : Function.Surjective (S'.orthogonalProjectionOnto : F →ₗ[𝕜] S') :=
        fun x => ⟨x, S'.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
      exact LinearMap.range_eq_top.mpr (TensorProduct.map_surjective h₁ h₂)
  exact (starProjection_inj.mpr hr.symm).trans hp'.symm

/-- **Definition `d:vs`.** A subspace `S ⊆ E` is `δ`-viable for `T ⊆ E ⊗ F` when `S ⊗ F` is
`δ`-close to `T`, that is, `P_T P_{S ⊗ F} P_T ≥ (1 - δ) P_T`. Arad, Landau, Vazirani and Vidick,
arXiv:1602.08828v2, Definition `d:vs` (lines 433–440). -/
def IsViable (δ : ℝ) (S : Submodule 𝕜 E) (T : Submodule 𝕜 (E ⊗[𝕜] F)) : Prop :=
  IsCloseTo δ (S.tensorProd ⊤) T

/-- **Lemma `l:t` (tensoring).** If `S₁ ⊆ E` and `S₂ ⊆ F` are `δ₁`-viable and `δ₂`-viable for
`T ⊆ E ⊗ F ⊗ G`, then `S₁ ⊗ S₂` is `(δ₁ + δ₂)`-viable for `T`. The viability of `S₁` is that
of `S₁ ⊗ F`, and the viability of `S₂` that of `E ⊗ S₂`. Arad, Landau, Vazirani and Vidick,
arXiv:1602.08828v2, Lemma `l:t` (lines 500–523). -/
theorem IsViable.tensorProd {δ₁ δ₂ : ℝ} {S₁ : Submodule 𝕜 E} {S₂ : Submodule 𝕜 F}
    {T : Submodule 𝕜 ((E ⊗[𝕜] F) ⊗[𝕜] G)} (h₁ : IsViable δ₁ (S₁.tensorProd (⊤ : Submodule 𝕜 F)) T)
    (h₂ : IsViable δ₂ ((⊤ : Submodule 𝕜 E).tensorProd S₂) T) :
    IsViable (δ₁ + δ₂) (S₁.tensorProd S₂) T := by
  unfold IsViable at *
  set U₁ := (S₁.tensorProd (⊤ : Submodule 𝕜 F)).tensorProd (⊤ : Submodule 𝕜 G)
  set U₂ := ((⊤ : Submodule 𝕜 E).tensorProd S₂).tensorProd (⊤ : Submodule 𝕜 G)
  have hP₁ : U₁.starProjection = mapL (mapL S₁.starProjection 1) 1 := by
    rw [starProjection_tensorProd, starProjection_tensorProd, starProjection_top',
      starProjection_top']
  have hP₂ : U₂.starProjection = mapL (mapL 1 S₂.starProjection) 1 := by
    rw [starProjection_tensorProd, starProjection_tensorProd, starProjection_top',
      starProjection_top']
  have hc : Commute U₁.starProjection U₂.starProjection := by
    rw [hP₁, hP₂]
    change _ * _ = _ * _
    rw [← mapL_mul, ← mapL_mul, ← mapL_mul, ← mapL_mul]
    simp only [mul_one, one_mul]
  have heq : U₁ ⊓ U₂ = (S₁.tensorProd S₂).tensorProd ⊤ := by
    refine starProjection_inj.mp ?_
    rw [starProjection_inf_of_commute hc, hP₁, hP₂, ← mapL_mul, ← mapL_mul,
      starProjection_tensorProd, starProjection_tensorProd, starProjection_top']
    simp only [mul_one, one_mul]
  rw [← heq]
  exact h₁.inf_of_commute h₂ hc

end Submodule
