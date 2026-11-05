/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTensor

/-!
# Images of finite tensor families

A finite tensor decomposition sends a retained subspace tensored with its
whole environment into the span of the retained-factor images tensored
with that same environment. This is the containment argument in ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 606–622. No contraction or
identity on a spectral band is used in this algebraic step.
-/

open scoped TensorProduct InnerProductSpace BigOperators
open TensorProduct Module

namespace Submodule

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

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The actual tensor-decomposed image is contained in the retained-factor
family span, with the whole environment left unrestricted. This is the
containment step of ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 606–622. -/
theorem map_tensorProd_top_le_iSup_map {ι : Type*} [Fintype ι]
    (S : Submodule 𝕜 E) (A : ι → E →L[𝕜] E) (B : ι → F →L[𝕜] F)
    {K : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F}
    (hdec : K = ∑ i, mapL (A i) (B i)) :
    (S.tensorProd (⊤ : Submodule 𝕜 F)).map K.toLinearMap ≤
      (⨆ i, S.map (A i : E →ₗ[𝕜] E)).tensorProd (⊤ : Submodule 𝕜 F) := by
  rw [map_le_iff_le_comap, tensorProd_le_iff]
  intro x hx y _
  change K (x ⊗ₜ[𝕜] y) ∈
    (⨆ i, S.map (A i : E →ₗ[𝕜] E)).tensorProd (⊤ : Submodule 𝕜 F)
  rw [hdec, _root_.sum_apply]
  refine sum_mem fun i _ ↦ ?_
  rw [mapL_tmul]
  exact tmul_mem_tensorProd (mem_iSup_of_mem i (mem_map_of_mem hx)) mem_top

end Submodule
