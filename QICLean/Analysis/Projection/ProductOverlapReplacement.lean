/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Product replacement in two subspaces

Let a unit vector lie in the tensor product of two subspaces that admit orthogonal
projections. For any product target, there are unit vectors in the same subspaces
whose product has at least as large an absolute overlap with the target.

Project each target factor onto its subspace and normalize. If a projection vanishes,
choose an arbitrary unit vector in that subspace. The existence of the original unit
tensor ensures that neither subspace is zero. Cauchy–Schwarz gives the comparison.

This is the Hilbert-space step in the product replacement argument of Schuch, Wolf,
Verstraete, and Cirac, arXiv:0705.0292v2, the footnote at lines 436–470 of
`paper_v2.tex`. Preservation of matrix product state bond dimensions is a separate
application to the boundary subspaces.
-/

open scoped TensorProduct InnerProductSpace

namespace TensorProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem exists_unit_inner_norm [Nontrivial E] (a : E) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖inner ℂ a u‖ = ‖a‖ := by
  by_cases ha : a = 0
  · obtain ⟨u, hu⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    exact ⟨u, hu, by simp [ha]⟩
  · refine ⟨NormedSpace.normalize a, NormedSpace.norm_normalize ha, ?_⟩
    simp [NormedSpace.normalize, inner_smul_right_eq_smul,
      inner_self_eq_norm_sq_to_K, pow_two, norm_ne_zero_iff.mpr ha]

/-- A unit vector in a tensor product cannot overlap a pure tensor more than a
suitable unit pure tensor does. Source: arXiv:0705.0292v2, footnote at lines 436–470. -/
private theorem exists_unit_product_overlap_ge [Nontrivial E] [Nontrivial F]
    (a : E) (b : F) (Φ : E ⊗[ℂ] F) (hΦ : ‖Φ‖ = 1) :
    ∃ (u : E) (v : F), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ‖inner ℂ (a ⊗ₜ[ℂ] b) Φ‖ ≤ ‖inner ℂ a u‖ * ‖inner ℂ b v‖ := by
  obtain ⟨u, hu, hau⟩ := exists_unit_inner_norm a
  obtain ⟨v, hv, hbv⟩ := exists_unit_inner_norm b
  refine ⟨u, v, hu, hv, ?_⟩
  simpa [hau, hbv, hΦ, norm_tmul] using norm_inner_le_norm (𝕜 := ℂ) (a ⊗ₜ[ℂ] b) Φ

private theorem inner_mapIncl_eq_inner_projection
    (U : Submodule ℂ E) (V : Submodule ℂ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (a : E) (b : F) (Φ : U ⊗[ℂ] V) :
    inner ℂ (a ⊗ₜ[ℂ] b) (mapIncl U V Φ) =
      inner ℂ (U.orthogonalProjectionOnto a ⊗ₜ[ℂ] V.orthogonalProjectionOnto b) Φ := by
  induction Φ using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [mapIncl, map_tmul, Submodule.subtype_apply, inner_tmul,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  | add x y hx hy =>
    rw [map_add, inner_add_right, hx, hy]
    exact (inner_add_right (𝕜 := ℂ)
      (U.orthogonalProjectionOnto a ⊗ₜ[ℂ] V.orthogonalProjectionOnto b) x y).symm

/-- Within two subspaces, a unit pure tensor attains at least the overlap of any
unit tensor with a product target. Source: arXiv:0705.0292v2, lines 436–470. -/
theorem exists_unit_product_overlap_ge_of_subspaces
    (U : Submodule ℂ E) (V : Submodule ℂ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (a : E) (b : F) (Φ : U ⊗[ℂ] V) (hΦ : ‖Φ‖ = 1) :
    ∃ (u : U) (v : V), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ‖inner ℂ (a ⊗ₜ[ℂ] b) (mapIncl U V Φ)‖ ≤
        ‖inner ℂ a (u : E)‖ * ‖inner ℂ b (v : F)‖ := by
  have hΦ0 : Φ ≠ 0 := fun hz ↦ zero_ne_one
    ((@norm_zero (U ⊗[ℂ] V) _).symm.trans ((congrArg norm hz).symm.trans hΦ))
  rcases subsingleton_or_nontrivial U with hU | hU
  · exact (hΦ0 (Subsingleton.elim _ _)).elim
  · rcases subsingleton_or_nontrivial V with hV | hV
    · exact (hΦ0 (Subsingleton.elim _ _)).elim
    · simpa only [inner_mapIncl_eq_inner_projection,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using
        exists_unit_product_overlap_ge (U.orthogonalProjectionOnto a)
          (V.orthogonalProjectionOnto b) Φ hΦ

end TensorProduct

open Matrix

namespace Matrix

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A matrix vector belongs to the tensor product of its column and row spaces. -/
private theorem exists_tensor_range (C : Matrix α β ℂ) :
    ∃ θ : LinearMap.range (toEuclideanLin C) ⊗[ℂ]
        LinearMap.range (toEuclideanLin Cᵀ),
      ((EuclideanSpace.basisFun α ℂ).tensorProduct (EuclideanSpace.basisFun β ℂ)).repr
        (TensorProduct.mapIncl _ _ θ) = WithLp.toLp 2 (fun ij : α × β ↦ C ij.1 ij.2) := by
  classical
  refine ⟨∑ a : α,
    ((LinearMap.range (toEuclideanLin C)).orthogonalProjectionOnto
      (EuclideanSpace.basisFun α ℂ a)) ⊗ₜ[ℂ]
    ((toEuclideanLin Cᵀ).rangeRestrict (EuclideanSpace.basisFun α ℂ a)), ?_⟩
  ext ⟨a, b⟩
  simp only [EuclideanSpace.basisFun_apply, map_sum, TensorProduct.map_tmul,
    Submodule.subtype_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    LinearMap.codRestrict_apply, WithLp.ofLp_sum, Finset.sum_apply,
    OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
    ofLp_toLpLin, PiLp.ofLp_single, toLin'_apply, mulVec_single, MulOpposite.op_one,
    col_transpose, Pi.smul_apply, row_apply, one_smul]
  have hfix := Submodule.starProjection_mem_subspace_eq_self
    ((toEuclideanLin C).rangeRestrict (EuclideanSpace.basisFun β ℂ b))
  change (toEuclideanLin C).range.starProjection
      (toEuclideanLin C (EuclideanSpace.basisFun β ℂ b)) =
    toEuclideanLin C (EuclideanSpace.basisFun β ℂ b) at hfix
  conv_lhs at hfix =>
    rw [← (EuclideanSpace.basisFun α ℂ).sum_repr
      (toEuclideanLin C (EuclideanSpace.basisFun β ℂ b))]
  simpa [map_sum, EuclideanSpace.basisFun_apply] using
    congrArg (fun x : EuclideanSpace ℂ α ↦ x a) hfix

/-- A normalized coefficient matrix admits unit factors in its column and row spaces
whose product overlap with any product target is no smaller.
Source: arXiv:0705.0292v2, the footnote at lines 436–470. -/
theorem exists_unit_product_overlap_ge (C : Matrix α β ℂ)
    (hC : ‖WithLp.toLp 2 (fun ij : α × β ↦ C ij.1 ij.2)‖ = 1)
    (a : EuclideanSpace ℂ α) (b : EuclideanSpace ℂ β) :
    ∃ (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β),
      ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      u ∈ LinearMap.range (toEuclideanLin C) ∧
      v ∈ LinearMap.range (toEuclideanLin Cᵀ) ∧
      ‖inner ℂ (WithLp.toLp 2 (fun ij : α × β ↦ a ij.1 * b ij.2))
        (WithLp.toLp 2 (fun ij : α × β ↦ C ij.1 ij.2))‖ ≤
          ‖inner ℂ a u‖ * ‖inner ℂ b v‖ := by
  obtain ⟨θ, hθ⟩ := exists_tensor_range C
  have hnorm : ‖θ‖ = 1 := by
    simpa only [LinearIsometryEquiv.norm_map, ← TensorProduct.mapInclIsometry_apply,
      LinearIsometry.norm_map, hC] using congrArg norm hθ
  obtain ⟨u, v, hu, hv, huv⟩ := TensorProduct.exists_unit_product_overlap_ge_of_subspaces
    (LinearMap.range (toEuclideanLin C)) (LinearMap.range (toEuclideanLin Cᵀ)) a b θ hnorm
  refine ⟨u, v, hu, hv, u.property, v.property, ?_⟩
  have hprod : ((EuclideanSpace.basisFun α ℂ).tensorProduct
      (EuclideanSpace.basisFun β ℂ)).repr (a ⊗ₜ[ℂ] b) =
        WithLp.toLp 2 (fun ij : α × β ↦ a ij.1 * b ij.2) := by
    ext ij
    simp [OrthonormalBasis.tensorProduct_repr_tmul_apply', mul_comm]
  simpa only [← hprod, ← hθ, LinearIsometryEquiv.inner_map_map] using huv

end Matrix
