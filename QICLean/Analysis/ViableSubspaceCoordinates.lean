/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSpectralProjector
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Basis.Basic

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


section

section

open scoped TensorProduct

namespace Submodule

/-- The images of a nonzero subspace under all matrix units of a basis span
the whole space. No finiteness or nonempty-index hypothesis is required.
For a finite configuration basis this is the short-middle alternative in
ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
theorem iSup_map_basis_matrixUnits_eq_top
    {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (b : Module.Basis ι 𝕜 E) (S : Submodule 𝕜 E) (hS : S ≠ ⊥) :
    (⨆ i : ι, ⨆ j : ι, S.map ((b.coord j).smulRight (b i))) = ⊤ := by
  classical
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hS
  have hcoord : ¬∀ j, b.coord j v = 0 := fun h ↦
    hv0 (b.forall_coord_eq_zero_iff.mp h)
  obtain ⟨j, hj⟩ := not_forall.mp hcoord
  apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
  intro i
  refine mem_iSup_of_mem i (mem_iSup_of_mem j ?_)
  refine mem_map.mpr ⟨(b.coord j v)⁻¹ • v, S.smul_mem _ hv, ?_⟩
  simp only [LinearMap.smulRight_apply, map_smul, smul_smul,
    inv_mul_cancel₀ hj, one_smul]
end Submodule

namespace Submodule

/-- A viable subspace with error below one is nonzero when its target is
nonzero. This uses the existing projection characterization of viability.
Supporting ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440,
and the short-middle case of Theorem `t:ais`, lines 1010–1024. -/
theorem isViable_ne_bot_of_target_ne_bot
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {δ : ℝ} {S : Submodule ℂ E} {T : Submodule ℂ (E ⊗[ℂ] F)}
    (hviable : IsViable δ S T) (hδ : δ < 1) (hT : T ≠ ⊥) : S ≠ ⊥ := by
  intro hS
  obtain ⟨t, ht, ht0⟩ := T.ne_bot_iff.mp hT
  unfold IsViable at hviable
  have hbound := (isCloseTo_iff.mp hviable) t ht
  rw [starProjection_tensorProd, hS, starProjection_bot,
    TensorProduct.mapL_zero_left, zero_apply, norm_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0)] at hbound
  have hpos : 0 < (1 - δ) * ‖t‖ ^ 2 :=
    mul_pos (sub_pos.mpr hδ) (sq_pos_of_pos (norm_pos_iff.mpr ht0))
  exact (not_le.mpr hpos) hbound
end Submodule
end

section

namespace Submodule

/-- Extending a finite operator family by zero preserves the span of its
images of every subspace. The extension is chosen before the subspace.
Auxiliary to the fixed collection of operators in ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. Empty families and
zero-dimensional spaces are included; no viability or spectral hypothesis
is required for this algebraic identity. -/
theorem exists_clm_family_extension_of_card_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] {M : ℕ}
    (hNM : Fintype.card ι ≤ M) (A : ι → E →L[ℂ] E) :
    ∃ (f : ι ↪ Fin M) (B : Fin M → E →L[ℂ] E),
      (∀ i, B (f i) = A i) ∧ (∀ j, j ∉ Set.range f → B j = 0) ∧
      ∀ S : Submodule ℂ E,
        (⨆ j, S.map (B j : E →ₗ[ℂ] E)) = (⨆ i, S.map (A i : E →ₗ[ℂ] E)) := by
  classical
  obtain ⟨f⟩ : Nonempty (ι ↪ Fin M) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hNM)
  let B : Fin M → E →L[ℂ] E := Function.extend f A 0
  have hB (i : ι) : B (f i) = A i := f.injective.extend_apply _ _ i
  have hBzero (j : Fin M) (hj : j ∉ Set.range f) : B j = 0 :=
    Function.extend_apply' (f := f) A (0 : Fin M → E →L[ℂ] E) j
      (by simpa only [Set.mem_range] using hj)
  refine ⟨f, B, hB, hBzero, ?_⟩
  intro S
  refine le_antisymm (iSup_le fun j ↦ ?_) (iSup_le fun i ↦ ?_)
  · by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [hB i]
      exact le_iSup (fun r ↦ S.map (A r : E →ₗ[ℂ] E)) i
    · simp only [hBzero j hj, ContinuousLinearMap.toLinearMap_zero, Submodule.map_zero]
      exact bot_le
  · rw [← hB i]
    exact le_iSup (fun r ↦ S.map (B r : E →ₗ[ℂ] E)) (f i)
end Submodule
end
end
