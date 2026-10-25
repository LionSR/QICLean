/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Error reduction of close subspaces

Arad, Landau, Vazirani and Vidick, *Rigorous RG algorithms and area laws for low energy
eigenstates in 1D* (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`), improve a viable set by applying
an approximate ground state projection `K` (Lemma `l:er`, lines 597–622). The operator step of
that proof is the following. Suppose `K` maps the target `T` and its orthogonal complement into
themselves, does not shrink vectors of `T`, and shrinks squared norms on `Tᗮ` by the factor `Δ`.
If `U` is `δ`-close to `T` with `δ < 1`, then the image `K U` is `Δ / (1 - δ) ^ 2`-close to `T`.
For a spectral approximate ground state projection `K = ∑ i, L_i ⊗ A_i ⊗ R_i` and
`U = H_L ⊗ S ⊗ H_R`, the image `K U` lies in `H_L ⊗ V ⊗ H_R` with `V = span {A_i S}`, so `V` is
`Δ / (1 - δ) ^ 2`-viable by monotonicity of closeness.

The hypotheses are stated on `T` and `Tᗮ` directly. The tensor-product statement of Lemma `l:er`,
with `T` the spectral subspace of a Hamiltonian, is not formalized here.

## Main statements

* `Submodule.IsCloseTo.mono`: a larger subspace stays close.
* `Submodule.IsCloseTo.map_of_contract`: the operator step of Lemma `l:er`.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Closeness to `T` passes to every larger subspace. -/
theorem IsCloseTo.mono {δ : ℝ} {U U' T : Submodule 𝕜 E} (h : IsCloseTo δ U T) (hU : U ≤ U') :
    IsCloseTo δ U' T := by
  rw [isCloseTo_iff] at h ⊢
  intro t ht
  refine (h t ht).trans ?_
  have hle : ‖U.starProjection t‖ ≤ ‖U'.starProjection t‖ := by
    have := congrArg (fun A : E →L[𝕜] E => A t) (starProjection_comp_starProjection_of_le hU)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this]
    exact U.norm_starProjection_apply_le _
  gcongr

/-- **The operator step of Lemma `l:er` (error reduction).** Let `K` map `T` and `Tᗮ` into
themselves, with `‖t‖ ≤ ‖K t‖` on `T` and `‖K q‖ ^ 2 ≤ Δ ‖q‖ ^ 2` on `Tᗮ`. If `U` is `δ`-close
to `T` with `δ < 1`, then `K U` is `Δ / (1 - δ) ^ 2`-close to `T`. Arad, Landau, Vazirani and
Vidick, arXiv:1602.08828v2, proof of Lemma `l:er` (lines 606–622); the tensor-product statement
itself is not formalized here. -/
theorem IsCloseTo.map_of_contract {δ Δ : ℝ} {U T : Submodule 𝕜 E} (K : E →L[𝕜] E)
    (h : IsCloseTo δ U T) (hδ : δ < 1) (hΔ : 0 ≤ Δ) (hKT : ∀ t ∈ T, K t ∈ T)
    (hKTo : ∀ q ∈ Tᗮ, K q ∈ Tᗮ) (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ q ∈ Tᗮ, ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2) :
    IsCloseTo (Δ / (1 - δ) ^ 2) (U.map K.toLinearMap) T := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  rw [isCloseTo_iff]
  intro t ht
  -- A preimage `r ∈ T` of `t` under `K`.
  obtain ⟨r, hrT, hKr⟩ : ∃ r ∈ T, K r = t := by
    let f : T →ₗ[𝕜] T := (K.toLinearMap ∘ₗ T.subtype).codRestrict T fun x => hKT x x.2
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have h0 : K x = 0 := congrArg Subtype.val hx
      have := hlow x x.2
      rw [h0, norm_zero] at this
      exact Subtype.ext (norm_le_zero_iff.mp this)
    obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨t, ht⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hr : ‖r‖ ≤ ‖t‖ := hKr ▸ hlow r hrT
  obtain ⟨u, hu, hPu, hun⟩ := h.exists_mem_starProjection_eq hδ hrT
  have h1δ : 0 < 1 - δ := by linarith
  have hut : ‖u‖ ≤ ‖t‖ / (1 - δ) := hun.trans (div_le_div_of_nonneg_right hr h1δ.le)
  -- The component `q = u - r` of `u` orthogonal to `T`.
  set q := u - r with hq_def
  have hq : q ∈ Tᗮ := by
    rw [hq_def, ← hPu]
    exact T.sub_starProjection_mem_orthogonal u
  have hqu : ‖q‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have := norm_sq_eq_add_norm_sq_starProjection u T
    rw [starProjection_orthogonal_val, hPu] at this
    nlinarith [sq_nonneg ‖r‖]
  have hy : ‖K q‖ ^ 2 ≤ Δ / (1 - δ) ^ 2 * ‖t‖ ^ 2 := by
    calc ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2 := hhigh q hq
      _ ≤ Δ * (‖t‖ / (1 - δ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (hqu.trans (pow_le_pow_left₀ (norm_nonneg _) hut 2)) hΔ
      _ = Δ / (1 - δ) ^ 2 * ‖t‖ ^ 2 := by rw [div_pow]; ring
  -- `K u = t + K q` with orthogonal summands.
  have hKu : K u = t + K q := by
    rw [hq_def, map_sub, hKr, add_sub_cancel]
  have horth : ⟪t, K q⟫_𝕜 = 0 := inner_right_of_mem_orthogonal ht (hKTo q hq)
  have hnKu : ‖K u‖ ^ 2 = ‖t‖ ^ 2 + ‖K q‖ ^ 2 := by
    rw [hKu, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  -- The overlap of `K u ∈ K U` with `t`.
  set P := (U.map K.toLinearMap).starProjection
  have hmem : K u ∈ U.map K.toLinearMap := mem_map_of_mem hu
  have hinner : ⟪K u, P t⟫_𝕜 = (‖t‖ ^ 2 : 𝕜) := by
    rw [← (U.map K.toLinearMap).inner_starProjection_left_eq_right,
      (U.map K.toLinearMap).starProjection_eq_self_iff.mpr hmem, hKu, inner_add_left,
      inner_left_of_mem_orthogonal ht (hKTo q hq), add_zero, inner_self_eq_norm_sq_to_K]
  have hov : ‖t‖ ^ 2 ≤ ‖K u‖ * ‖P t‖ := by
    have := norm_inner_le_norm (𝕜 := 𝕜) (K u) (P t)
    rw [hinner, ← RCLike.ofReal_pow, RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at this
    exact this
  have hsq : ‖t‖ ^ 2 * ‖t‖ ^ 2 ≤ (‖t‖ ^ 2 + ‖K q‖ ^ 2) * ‖P t‖ ^ 2 := by
    rw [← hnKu]
    have h0 : 0 ≤ ‖t‖ ^ 2 := by positivity
    nlinarith [mul_le_mul hov hov h0 (by positivity)]
  set x := ‖t‖ ^ 2
  set y := ‖K q‖ ^ 2
  set p := ‖P t‖ ^ 2
  have hx : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hp : 0 ≤ p := by positivity
  by_contra hcon
  push Not at hcon
  -- `p < x - y`, so `(x + y) p < x ^ 2 - y ^ 2 ≤ x ^ 2`.
  have hpxy : p < x - y := by linarith
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0] at hcon
    linarith
  · nlinarith [mul_lt_mul_of_pos_left hpxy (by linarith : 0 < x + y)]

end Submodule
