/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates

/-!
# Tensor coordinates for viable subspaces

Transporting each factor by a linear isometry transports the actual tensor
product subspace. These identities support the tensoring argument in ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523.
-/

open scoped TensorProduct

namespace Submodule

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- Tensor product subspaces are transported by the actual factor isometries.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma map_tensorProd_congrIsometry (f : E ≃ₗᵢ[𝕜] E') (g : F ≃ₗᵢ[𝕜] F')
    (S : Submodule 𝕜 E) (T : Submodule 𝕜 F) :
    (S.tensorProd T).map (TensorProduct.congrIsometry f g).toLinearEquiv.toLinearMap =
      (S.map f.toLinearEquiv.toLinearMap).tensorProd
        (T.map g.toLinearEquiv.toLinearMap) := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, tensorProd_le_iff]
    intro x hx y hy
    change f x ⊗ₜ[𝕜] g y ∈
      (S.map f.toLinearEquiv.toLinearMap).tensorProd (T.map g.toLinearEquiv.toLinearMap)
    exact tmul_mem_tensorProd ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · rw [tensorProd_le_iff]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x ⊗ₜ[𝕜] y, tmul_mem_tensorProd hx hy, rfl⟩

/-- Exchanging the actual tensor factors exchanges the tensor product subspaces.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma map_tensorProd_commIsometry (S : Submodule 𝕜 E) (T : Submodule 𝕜 F) :
    (S.tensorProd T).map (TensorProduct.commIsometry 𝕜 E F).toLinearEquiv.toLinearMap =
      T.tensorProd S := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, tensorProd_le_iff]
    intro x hx y hy
    exact tmul_mem_tensorProd hy hx
  · rw [tensorProd_le_iff]
    intro y hy x hx
    exact ⟨x ⊗ₜ[𝕜] y, tmul_mem_tensorProd hx hy, rfl⟩

/-- The tensor product of the two whole spaces is the whole tensor product.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
@[simp]
lemma tensorProd_top_top :
    (⊤ : Submodule 𝕜 E).tensorProd (⊤ : Submodule 𝕜 F) = ⊤ :=
  LinearMap.range_eq_top.mpr (TensorProduct.map_surjective
    (fun x ↦ ⟨⟨x, trivial⟩, rfl⟩) (fun x ↦ ⟨⟨x, trivial⟩, rfl⟩))

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Associating the actual tensor product subspaces changes no vectors.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma map_tensorProd_assocIsometry (S : Submodule 𝕜 E) (T : Submodule 𝕜 F)
    (U : Submodule 𝕜 G) :
    ((S.tensorProd T).tensorProd U).map
      (TensorProduct.assocIsometry 𝕜 E F G).toLinearEquiv.toLinearMap =
      S.tensorProd (T.tensorProd U) := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, tensorProd_le_iff]
    rintro _ ⟨w, rfl⟩ z hz
    change TensorProduct.assoc 𝕜 E F G
      (TensorProduct.map S.subtype T.subtype w ⊗ₜ[𝕜] z) ∈ S.tensorProd (T.tensorProd U)
    induction w with
    | tmul x y =>
      rw [TensorProduct.map_tmul, TensorProduct.assoc_tmul]
      exact tmul_mem_tensorProd x.2 (tmul_mem_tensorProd y.2 hz)
    | add w w' hw hw' =>
      rw [map_add, TensorProduct.add_tmul, map_add]
      exact add_mem hw hw'
  · rw [tensorProd_le_iff]
    rintro x hx _ ⟨w, rfl⟩
    induction w with
    | tmul y z =>
      rw [TensorProduct.map_tmul]
      exact ⟨(x ⊗ₜ[𝕜] (y : F)) ⊗ₜ[𝕜] (z : G),
        tmul_mem_tensorProd (tmul_mem_tensorProd hx y.2) z.2, rfl⟩
    | add w w' hw hw' =>
      rw [map_add, TensorProduct.tmul_add]
      exact add_mem hw hw'

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 E'] [FiniteDimensional 𝕜 F']

/-- The actual tensor product subspace has dimension at most the product
of the input dimensions. Supporting ALVV, arXiv:1602.08828v2,
Lemma `l:t`, lines 500–523. -/
lemma finrank_tensorProd_le (S : Submodule 𝕜 E) (T : Submodule 𝕜 F) :
    Module.finrank 𝕜 (S.tensorProd T) ≤ Module.finrank 𝕜 S * Module.finrank 𝕜 T := by
  calc
    _ ≤ Module.finrank 𝕜 (S ⊗[𝕜] T) :=
      LinearMap.finrank_range_le (TensorProduct.map S.subtype T.subtype)
    _ = _ := Module.finrank_tensorProduct

/-- Viability is invariant under actual isometries of both tensor factors.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma isViable_map_congrIsometry_iff (f : E ≃ₗᵢ[𝕜] E') (g : F ≃ₗᵢ[𝕜] F')
    {delta : ℝ} (S : Submodule 𝕜 E) (T : Submodule 𝕜 (E ⊗[𝕜] F)) :
    IsViable delta (S.map f.toLinearEquiv.toLinearMap)
      (T.map (TensorProduct.congrIsometry f g).toLinearEquiv.toLinearMap) ↔
      IsViable delta S T := by
  unfold IsViable
  have hmap := map_tensorProd_congrIsometry f g S ⊤
  simp only [map_top, LinearEquiv.range] at hmap
  rw [← hmap, isCloseTo_map_iff]

variable [FiniteDimensional 𝕜 G]

/-- Viability on the first factor equals viability of its extension to the
first two factors before reassociation. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma isViable_map_assocIsometry_iff {delta : ℝ} (S : Submodule 𝕜 E)
    (T : Submodule 𝕜 ((E ⊗[𝕜] F) ⊗[𝕜] G)) :
    IsViable delta S
      (T.map (TensorProduct.assocIsometry 𝕜 E F G).toLinearEquiv.toLinearMap) ↔
      IsViable delta (S.tensorProd (⊤ : Submodule 𝕜 F)) T := by
  unfold IsViable
  have hmap := map_tensorProd_assocIsometry S (⊤ : Submodule 𝕜 F) (⊤ : Submodule 𝕜 G)
  rw [tensorProd_top_top] at hmap
  rw [← hmap, isCloseTo_map_iff]

/-- Tensoring viability for one common three-factor target, expressed in
the actual first-factor and second-factor tensor splits. This is ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523, after reassociation. -/
lemma IsViable.tensorProd_of_factor_splits {delta1 delta2 : ℝ}
    (S1 : Submodule 𝕜 E) (S2 : Submodule 𝕜 F)
    (T : Submodule 𝕜 ((E ⊗[𝕜] F) ⊗[𝕜] G))
    (h1 : IsViable delta1 S1
      (T.map (TensorProduct.assocIsometry 𝕜 E F G).toLinearEquiv.toLinearMap))
    (h2 : IsViable delta2 S2
      ((T.map (TensorProduct.congrIsometry (TensorProduct.commIsometry 𝕜 E F)
        (LinearIsometryEquiv.refl 𝕜 G)).toLinearEquiv.toLinearMap).map
          (TensorProduct.assocIsometry 𝕜 F E G).toLinearEquiv.toLinearMap)) :
    IsViable (delta1 + delta2) (S1.tensorProd S2) T := by
  have hfirst := (isViable_map_assocIsometry_iff S1 T).mp h1
  have hsecond' := (isViable_map_assocIsometry_iff S2 _).mp h2
  have hsecond : IsViable delta2 ((⊤ : Submodule 𝕜 E).tensorProd S2) T := by
    apply (isViable_map_congrIsometry_iff (TensorProduct.commIsometry 𝕜 E F)
      (LinearIsometryEquiv.refl 𝕜 G) ((⊤ : Submodule 𝕜 E).tensorProd S2) T).mp
    simpa only [map_tensorProd_commIsometry] using hsecond'
  exact hfirst.tensorProd hsecond

section Coordinates

variable {sigma beta kappa : Type*} [Fintype sigma] [Fintype beta] [Fintype kappa]
  [DecidableEq sigma] [DecidableEq beta]

/-- Reindexing configurations before the Euclidean tensor split gives the
actual product of the two factor coordinates. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma euclideanTensorEquiv_reindex_symm_tmul (e : kappa ≃ sigma × beta)
    (x : EuclideanSpace ℂ sigma) (y : EuclideanSpace ℂ beta) (c : kappa) :
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).trans
      (euclideanTensorEquiv sigma beta)).symm (x ⊗ₜ[ℂ] y) c =
      x (e c).1 * y (e c).2 := by
  simp only [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply]
  change (euclideanTensorEquiv sigma beta).symm (x ⊗ₜ[ℂ] y) (e c) = _
  exact euclideanTensorEquiv_symm_tmul x y _ _

end Coordinates

end Submodule
