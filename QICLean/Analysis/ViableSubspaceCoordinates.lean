/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSpectralProjector

/-!
# Viable subspaces in coordinates

Arad, Landau, Vazirani and Vidick call `S ⊆ H_A` `δ`-viable for `T ⊆ H_A ⊗ H_B` when
`S ⊗ H_B` is `δ`-close to `T` (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `d:vs`,
lines 433–440). `Submodule.IsViable` states this on Mathlib's tensor product `E ⊗[ℂ] F`. When
`H_A = ℂ^σ` and `H_B = ℂ^β` carry coordinates, as for the configurations of a chain of sites, it
is convenient to work in `ℂ^{σ × β}` instead, where `S ⊗ ℂ^β` is the subspace of vectors whose
slices `w (·, b)` all lie in `S`.

The two forms are related by the linear isometry `ℂ^{σ × β} ≅ ℂ^σ ⊗ ℂ^β` sending the coordinate
vector of `(a, b)` to `e_a ⊗ e_b`. It carries the coordinate extension of `S` onto
`S ⊗ ℂ^β` (`Submodule.map_prodExt_euclideanTensorEquiv`), and linear isometries preserve
closeness (`Submodule.isCloseTo_map_iff`), so viability transfers in both directions
(`Submodule.isCloseTo_prodExt_iff_isViable`).

## Main definitions

* `Submodule.prodExt`: the coordinate extension `S ⊗ ℂ^β ⊆ ℂ^{σ × β}`.
* `Submodule.euclideanTensorEquiv`: the linear isometry `ℂ^{σ × β} ≅ ℂ^σ ⊗ ℂ^β`.

## Main results

* `Submodule.isCloseTo_map_iff`: closeness is invariant under linear isometries.
* `Submodule.map_prodExt_euclideanTensorEquiv`: the isometry carries `prodExt S β` onto
  `S.tensorProd ⊤`.
* `Submodule.isCloseTo_prodExt_iff_isViable`: viability in coordinates is viability in the
  tensor product.
-/

open scoped TensorProduct InnerProductSpace
open TensorProduct

namespace Submodule

section Isometry

variable {𝕜 E E' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']

/-- **Closeness is invariant under linear isometries.** `Φ U` is `δ`-close to `Φ T` exactly
when `U` is `δ`-close to `T`. -/
theorem isCloseTo_map_iff (Φ : E ≃ₗᵢ[𝕜] E') {δ : ℝ} {U T : Submodule 𝕜 E} :
    IsCloseTo δ (U.map (Φ.toLinearEquiv : E →ₗ[𝕜] E')) (T.map (Φ.toLinearEquiv : E →ₗ[𝕜] E')) ↔
      IsCloseTo δ U T := by
  rw [isCloseTo_iff, isCloseTo_iff]
  constructor
  · intro h t ht
    have := h (Φ t) ⟨t, ht, rfl⟩
    rwa [starProjection_map_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at this
  · rintro h _ ⟨t, ht, rfl⟩
    rw [starProjection_map_apply]
    simpa [LinearIsometryEquiv.symm_apply_apply] using h t ht

end Isometry

variable {σ β : Type*} [Fintype σ] [Fintype β]

/-- The coordinate extension `S ⊗ ℂ^β` of a subspace `S ⊆ ℂ^σ`: the vectors of `ℂ^{σ × β}`
whose slices `w (·, b)` all lie in `S`. -/
def prodExt (S : Submodule ℂ (EuclideanSpace ℂ σ)) (β : Type*) [Fintype β] :
    Submodule ℂ (EuclideanSpace ℂ (σ × β)) where
  carrier := {w | ∀ b, (WithLp.toLp 2 fun a ↦ w (a, b) : EuclideanSpace ℂ σ) ∈ S}
  add_mem' {w w'} hw hw' b := by
    have h : (WithLp.toLp 2 fun a ↦ (w + w') (a, b) : EuclideanSpace ℂ σ) =
        (WithLp.toLp 2 fun a ↦ w (a, b)) + WithLp.toLp 2 fun a ↦ w' (a, b) := by
      ext a; simp
    rw [h]
    exact S.add_mem (hw b) (hw' b)
  zero_mem' b := by
    have h : (WithLp.toLp 2 fun a ↦ (0 : EuclideanSpace ℂ (σ × β)) (a, b) :
        EuclideanSpace ℂ σ) = 0 := by
      ext a; simp
    rw [h]
    exact S.zero_mem
  smul_mem' c w hw b := by
    have h : (WithLp.toLp 2 fun a ↦ (c • w) (a, b) : EuclideanSpace ℂ σ) =
        c • WithLp.toLp 2 fun a ↦ w (a, b) := by
      ext a; simp
    rw [h]
    exact S.smul_mem c (hw b)

omit [Fintype σ] in
theorem mem_prodExt {S : Submodule ℂ (EuclideanSpace ℂ σ)} {w : EuclideanSpace ℂ (σ × β)} :
    w ∈ prodExt S β ↔ ∀ b, (WithLp.toLp 2 fun a ↦ w (a, b) : EuclideanSpace ℂ σ) ∈ S :=
  Iff.rfl

variable [DecidableEq σ] [DecidableEq β]

/-- The linear isometry `ℂ^{σ × β} ≅ ℂ^σ ⊗ ℂ^β` sending the coordinate vector of `(a, b)` to
`e_a ⊗ e_b`. -/
noncomputable def euclideanTensorEquiv (σ β : Type*) [Fintype σ] [Fintype β] [DecidableEq σ]
    [DecidableEq β] :
    EuclideanSpace ℂ (σ × β) ≃ₗᵢ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β :=
  ((EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun β ℂ)).repr.symm

/-- In coordinates, `x ⊗ y` is the vector `(a, b) ↦ x a * y b`. -/
theorem euclideanTensorEquiv_symm_tmul (x : EuclideanSpace ℂ σ) (y : EuclideanSpace ℂ β)
    (a : σ) (b : β) :
    (euclideanTensorEquiv σ β).symm (x ⊗ₜ[ℂ] y) (a, b) = x a * y b := by
  simp [euclideanTensorEquiv, mul_comm]

/-- **The isometry carries the coordinate extension onto `S ⊗ ℂ^β`.** -/
theorem map_prodExt_euclideanTensorEquiv (S : Submodule ℂ (EuclideanSpace ℂ σ)) :
    (prodExt S β).map ((euclideanTensorEquiv σ β).toLinearEquiv :
        EuclideanSpace ℂ (σ × β) →ₗ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β) =
      S.tensorProd (⊤ : Submodule ℂ (EuclideanSpace ℂ β)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    -- `w = ∑_b w (·, b) ⊗ e_b`
    have hsum : euclideanTensorEquiv σ β w =
        ∑ b, (WithLp.toLp 2 fun a ↦ w (a, b) : EuclideanSpace ℂ σ) ⊗ₜ[ℂ]
          EuclideanSpace.single b (1 : ℂ) := by
      apply (euclideanTensorEquiv σ β).symm.injective
      rw [LinearIsometryEquiv.symm_apply_apply, map_sum]
      ext ⟨a, b⟩
      simp [euclideanTensorEquiv_symm_tmul, PiLp.single_apply]
    change euclideanTensorEquiv σ β w ∈ _
    rw [hsum]
    exact sum_mem fun b _ ↦ tmul_mem_tensorProd (hw b) mem_top
  · rw [tensorProd_le_iff]
    intro x hx y _
    refine ⟨(euclideanTensorEquiv σ β).symm (x ⊗ₜ[ℂ] y), fun b ↦ ?_,
      (euclideanTensorEquiv σ β).apply_symm_apply _⟩
    have : (WithLp.toLp 2 fun a ↦ (euclideanTensorEquiv σ β).symm (x ⊗ₜ[ℂ] y) (a, b) :
        EuclideanSpace ℂ σ) = y b • x := by
      ext a
      simp [euclideanTensorEquiv_symm_tmul, mul_comm]
    rw [this]
    exact S.smul_mem _ hx

/-- **Viability in coordinates is viability in the tensor product.** `S ⊗ ℂ^β` is `δ`-close to
`T ⊆ ℂ^{σ × β}` exactly when `S` is `δ`-viable for the image of `T` in `ℂ^σ ⊗ ℂ^β`
(arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `d:vs`, lines 433–440). -/
theorem isCloseTo_prodExt_iff_isViable {δ : ℝ} (S : Submodule ℂ (EuclideanSpace ℂ σ))
    (T : Submodule ℂ (EuclideanSpace ℂ (σ × β))) :
    IsCloseTo δ (prodExt S β) T ↔
      IsViable δ S (T.map ((euclideanTensorEquiv σ β).toLinearEquiv :
        EuclideanSpace ℂ (σ × β) →ₗ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)) := by
  rw [IsViable, ← map_prodExt_euclideanTensorEquiv, isCloseTo_map_iff]

end Submodule
