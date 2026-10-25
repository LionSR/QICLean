/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTensor

/-!
# Weights of a vector of `W ⊗ F` along an orthonormal basis of `W`

Let `W` be a subspace of `M` and `w ∈ W ⊗ F`. Writing `w = ∑_j x_j ⊗ e_j` along an orthonormal
basis `e_j` of `F`, the positive operator `G = ∑_j |x_j⟩⟨x_j|` on `W` has an orthonormal
eigenbasis `f_k` with eigenvalues `μ_k ≥ 0`, and for every subspace `W' ≤ W`
`‖P_{W' ⊗ F} w‖² = ∑_k μ_k ‖P_{W'} f_k‖²`, with `∑_k μ_k = ‖w‖²`.

The basis and the weights depend on `w` but not on `W'`. Arad, Landau, Vazirani and Vidick use
this decomposition in the proof of Lemma `l:rs` (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`,
lines 539–541): a lower bound on `‖P_{W'} f_k‖²` for the `q = dim W` vectors `f_k` gives the
same lower bound on `‖P_{W' ⊗ F} w‖² / ‖w‖²`, which accounts for the factor `q` in the failure
probability.

## Main statements

* `TensorProduct.innerSlice`: the partial inner product `a ⊗ b ↦ ⟪v, b⟫ a`.
* `TensorProduct.norm_sq_sum_tmul`: `‖∑_j y_j ⊗ e_j‖² = ∑_j ‖y_j‖²`.
* `Submodule.exists_weights_norm_sq_starProjection_tensorProd`: the decomposition above.
-/

open scoped TensorProduct InnerProductSpace
open TensorProduct Module

namespace TensorProduct

variable {𝕜 M F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The partial inner product `a ⊗ b ↦ ⟪v, b⟫ a` against a vector `v` of the second factor. -/
noncomputable def innerSlice (v : F) : M ⊗[𝕜] F →ₗ[𝕜] M :=
  (TensorProduct.rid 𝕜 M).toLinearMap ∘ₗ (innerₛₗ 𝕜 v).lTensor M

omit [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 F] in
theorem innerSlice_tmul (v : F) (a : M) (b : F) : innerSlice v (a ⊗ₜ[𝕜] b) = ⟪v, b⟫_𝕜 • a := by
  simp [innerSlice]

omit [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 F] in
/-- A vector of `M ⊗ F` is the sum of its slices against an orthonormal basis of `F`. -/
theorem sum_innerSlice_tmul {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 F) (w : M ⊗[𝕜] F) :
    ∑ j, innerSlice (e j) w ⊗ₜ[𝕜] e j = w := by
  induction w with
  | tmul a b =>
    simp_rw [innerSlice_tmul, smul_tmul, ← tmul_sum, e.sum_repr']
  | add z z' hz hz' =>
    simp_rw [map_add, add_tmul, Finset.sum_add_distrib, hz, hz']

omit [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 F] in
/-- `‖∑_j y_j ⊗ e_j‖² = ∑_j ‖y_j‖²` for an orthonormal basis `e_j` of `F`. -/
theorem norm_sq_sum_tmul {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 F) (y : ι → M) :
    ‖∑ j, y j ⊗ₜ[𝕜] e j‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 := by
  classical
  have h : ⟪∑ j, y j ⊗ₜ[𝕜] e j, ∑ j, y j ⊗ₜ[𝕜] e j⟫_𝕜 = ∑ j, ⟪y j, y j⟫_𝕜 := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    simp_rw [inner_tmul, orthonormal_iff_ite.mp e.orthonormal]
    simp
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), h, map_sum]
  simp_rw [inner_self_eq_norm_sq (𝕜 := 𝕜)]

omit [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 F] in
theorem innerSlice_mapL_one (P : M →L[𝕜] M) (v : F) (z : M ⊗[𝕜] F) :
    innerSlice v (mapL P (1 : F →L[𝕜] F) z) = P (innerSlice v z) := by
  induction z with
  | tmul a b => simp [innerSlice_tmul]
  | add z z' hz hz' => simp only [map_add, hz, hz']

end TensorProduct

namespace Submodule

variable {𝕜 M F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Weights along an eigenbasis.** For `w ∈ W ⊗ F` there are an orthonormal basis `f` of `W`
and weights `μ_k ≥ 0` with `∑_k μ_k = ‖w‖²` such that `‖P_{W' ⊗ F} w‖² = ∑_k μ_k ‖P_{W'} f_k‖²`
for every subspace `W' ≤ W`. Proof of Lemma `l:rs` of arXiv:1602.08828v2 (lines 539–541). -/
theorem exists_weights_norm_sq_starProjection_tensorProd (W : Submodule 𝕜 M)
    {w : M ⊗[𝕜] F} (hw : w ∈ W.tensorProd (⊤ : Submodule 𝕜 F)) :
    ∃ (f : OrthonormalBasis (Fin (finrank 𝕜 W)) 𝕜 W) (μ : Fin (finrank 𝕜 W) → ℝ),
      (∀ k, 0 ≤ μ k) ∧ ∑ k, μ k = ‖w‖ ^ 2 ∧
      ∀ W' : Submodule 𝕜 M, W' ≤ W →
        ‖(W'.tensorProd (⊤ : Submodule 𝕜 F)).starProjection w‖ ^ 2 =
          ∑ k, μ k * ‖W'.starProjection (f k : M)‖ ^ 2 := by
  classical
  set e := stdOrthonormalBasis 𝕜 F
  set x : Fin (finrank 𝕜 F) → M := fun j => innerSlice (e j) w
  -- The slices lie in `W`.
  have hPw : (W.tensorProd (⊤ : Submodule 𝕜 F)).starProjection w = w :=
    starProjection_eq_self_iff.mpr hw
  have hx : ∀ j, x j ∈ W := by
    intro j
    have : x j = W.starProjection (x j) := by
      simp only [x]
      conv_lhs => rw [← hPw]
      rw [starProjection_tensorProd, starProjection_top', innerSlice_mapL_one]
    rw [this]
    exact W.starProjection_apply_mem _
  -- The projection of `w` slice by slice.
  have hproj : ∀ W' : Submodule 𝕜 M,
      ‖(W'.tensorProd (⊤ : Submodule 𝕜 F)).starProjection w‖ ^ 2 =
        ∑ j, ‖W'.starProjection (x j)‖ ^ 2 := by
    intro W'
    conv_lhs => rw [← sum_innerSlice_tmul e w]
    rw [starProjection_tensorProd, starProjection_top', map_sum]
    simp_rw [mapL_tmul, one_apply_eq_self]
    exact norm_sq_sum_tmul e _
  -- The operator `G = ∑_j |x_j⟩⟨x_j|` on `W`.
  set xW : Fin (finrank 𝕜 F) → W := fun j => ⟨x j, hx j⟩
  set G : W →ₗ[𝕜] W := ∑ j, (innerₛₗ 𝕜 (xW j)).smulRight (xW j)
  have hG : ∀ a : W, G a = ∑ j, ⟪xW j, a⟫_𝕜 • xW j := by
    intro a
    simp [G]
  have hGsymm : G.IsSymmetric := by
    intro a b
    rw [hG, hG, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
  set f := hGsymm.eigenvectorBasis rfl
  set μ := hGsymm.eigenvalues rfl
  have hGf : ∀ k, G (f k) = (μ k : 𝕜) • f k := hGsymm.apply_eigenvectorBasis rfl
  -- `∑_j |⟪x_j, a⟫|² = ∑_l μ_l |⟪f_l, a⟫|²` for `a ∈ W`.
  have hquad : ∀ a : W,
      ∑ j, ‖⟪xW j, a⟫_𝕜‖ ^ 2 = ∑ l, μ l * ‖⟪f l, a⟫_𝕜‖ ^ 2 := by
    intro a
    have h1 : RCLike.re ⟪a, G a⟫_𝕜 = ∑ j, ‖⟪xW j, a⟫_𝕜‖ ^ 2 := by
      rw [hG, inner_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, ← inner_conj_symm a (xW j), RCLike.mul_conj, ← RCLike.ofReal_pow,
        RCLike.ofReal_re]
    have hGa : G a = ∑ l, ((μ l : 𝕜) * ⟪f l, a⟫_𝕜) • f l := by
      conv_lhs => rw [← f.sum_repr' a]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, hGf, smul_smul, mul_comm]
    have hin := f.orthonormal.inner_sum (fun l => ⟪f l, a⟫_𝕜)
      (fun l => (μ l : 𝕜) * ⟪f l, a⟫_𝕜) Finset.univ
    rw [f.sum_repr'] at hin
    have h2 : RCLike.re ⟪a, G a⟫_𝕜 = ∑ l, μ l * ‖⟪f l, a⟫_𝕜‖ ^ 2 := by
      rw [hGa, hin, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [show (starRingEnd 𝕜) ⟪f l, a⟫_𝕜 * ((μ l : 𝕜) * ⟪f l, a⟫_𝕜) =
          (μ l : 𝕜) * ((starRingEnd 𝕜) ⟪f l, a⟫_𝕜 * ⟪f l, a⟫_𝕜) by ring, RCLike.conj_mul,
        ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    rw [← h1, h2]
  -- Parseval in `W`.
  have hpars : ∀ y ∈ W, ∑ k, ‖⟪(f k : M), y⟫_𝕜‖ ^ 2 = ‖y‖ ^ 2 := by
    intro y hy
    simpa [Submodule.coe_inner] using f.sum_sq_norm_inner_right (⟨y, hy⟩ : W)
  have hkey : ∀ W' : Submodule 𝕜 M, W' ≤ W →
      ∑ j, ‖W'.starProjection (x j)‖ ^ 2 = ∑ k, μ k * ‖W'.starProjection (f k : M)‖ ^ 2 := by
    intro W' hle
    have hmem : ∀ y, W'.starProjection y ∈ W := fun y => hle (W'.starProjection_apply_mem y)
    calc ∑ j, ‖W'.starProjection (x j)‖ ^ 2
        = ∑ j, ∑ k, ‖⟪xW j, (⟨W'.starProjection (f k : M), hmem _⟩ : W)⟫_𝕜‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hpars _ (hmem _)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Submodule.coe_inner, ← W'.inner_starProjection_left_eq_right, norm_inner_symm]
      _ = ∑ k, ∑ l, μ l * ‖⟪f l, (⟨W'.starProjection (f k : M), hmem _⟩ : W)⟫_𝕜‖ ^ 2 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => hquad _
      _ = ∑ l, μ l * ‖W'.starProjection (f l : M)‖ ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum, ← hpars _ (hmem _)]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Submodule.coe_inner, ← W'.inner_starProjection_left_eq_right, norm_inner_symm]
  refine ⟨f, μ, fun k => ?_, ?_, fun W' hle => (hproj W').trans (hkey W' hle)⟩
  · have h := hquad (f k)
    simp only [orthonormal_iff_ite.mp f.orthonormal] at h
    rw [Finset.sum_eq_single k (fun l _ hlk => by simp [hlk]) (by simp)] at h
    simp only [ite_true, norm_one, one_pow, mul_one] at h
    rw [← h]
    positivity
  · have h := (hproj W).trans (hkey W le_rfl)
    rw [hPw] at h
    have hf : ∀ k, ‖W.starProjection (f k : M)‖ = 1 := fun k => by
      rw [starProjection_eq_self_iff.mpr (f k).2, Submodule.norm_coe, f.orthonormal.1 k]
    simp only [hf, one_pow, mul_one] at h
    exact h.symm

end Submodule
