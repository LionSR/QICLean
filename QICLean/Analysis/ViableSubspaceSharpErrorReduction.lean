/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Sharp error reduction for close subspaces

The projection argument in ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
also yields a normalized error bound. Its ratio of error to success contracts by
exactly the squared-norm contraction factor. This auxiliary estimate is useful
when the filtering operator is applied repeatedly. The nested version allows
spectrum between two cutoffs, as in Theorem `t:aisgapless`, lines 1037–1041.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Normalized error reduction between nested targets. The stronger projection-preimage
estimate refines the argument of ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
and Theorem `t:aisgapless`, lines 1037–1041. No gap between the targets is assumed. -/
theorem IsCloseTo.map_of_nested_contract_sharp {δ Δ : ℝ} {U T Tplus : Submodule 𝕜 E}
    (K : E →L[𝕜] E) (hT : T ≤ Tplus)
    (h : IsCloseTo δ U Tplus) (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hΔ : 0 ≤ Δ)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ q ∈ Tplusᗮ, K q ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ q ∈ Tplusᗮ, ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2) :
    IsCloseTo (Δ * δ / (1 - δ + Δ * δ)) (U.map K.toLinearMap) T := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hc : 0 < 1 - δ := by linarith
  have hd : 0 < 1 - δ + Δ * δ := by positivity
  rw [isCloseTo_iff]
  intro t ht
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
  obtain ⟨u, hu, hPu, _, hun⟩ :=
    h.exists_mem_starProjection_eq_and_norm_sq_le hδ (hT hrT)
  set q := u - r with hq_def
  have hq : q ∈ Tplusᗮ := by
    rw [hq_def, ← hPu]
    exact Tplus.sub_starProjection_mem_orthogonal u
  have hpy : ‖u‖ ^ 2 = ‖r‖ ^ 2 + ‖q‖ ^ 2 := by
    have hh := norm_sq_eq_add_norm_sq_starProjection u Tplus
    rw [starProjection_orthogonal_val, hPu] at hh
    exact hh
  have hqn : ‖q‖ ^ 2 ≤ δ / (1 - δ) * ‖r‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have hh := (le_div_iff₀ hc).mp hun
    nlinarith
  have hy : ‖K q‖ ^ 2 ≤ Δ * δ / (1 - δ) * ‖t‖ ^ 2 := by
    calc
      ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2 := hhigh q hq
      _ ≤ Δ * (δ / (1 - δ) * ‖r‖ ^ 2) := mul_le_mul_of_nonneg_left hqn hΔ
      _ ≤ Δ * (δ / (1 - δ) * ‖t‖ ^ 2) := by gcongr
      _ = _ := by ring
  have hKu : K u = t + K q := by rw [hq_def, map_sub, hKr, add_sub_cancel]
  have horth : ⟪t, K q⟫_𝕜 = 0 := inner_right_of_mem_orthogonal ht (hKTo q hq)
  have hnKu : ‖K u‖ ^ 2 = ‖t‖ ^ 2 + ‖K q‖ ^ 2 := by
    rw [hKu, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  set P := (U.map K.toLinearMap).starProjection
  have hmem : K u ∈ U.map K.toLinearMap := mem_map_of_mem hu
  have hinner : ⟪K u, P t⟫_𝕜 = (‖t‖ ^ 2 : 𝕜) := by
    rw [← (U.map K.toLinearMap).inner_starProjection_left_eq_right,
      (U.map K.toLinearMap).starProjection_eq_self_iff.mpr hmem, hKu, inner_add_left,
      inner_left_of_mem_orthogonal ht (hKTo q hq), add_zero, inner_self_eq_norm_sq_to_K]
  have hov : ‖t‖ ^ 2 ≤ ‖K u‖ * ‖P t‖ := by
    have hh := norm_inner_le_norm (𝕜 := 𝕜) (K u) (P t)
    rw [hinner, ← RCLike.ofReal_pow, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity)] at hh
    exact hh
  have hsq : ‖t‖ ^ 2 * ‖t‖ ^ 2 ≤ (‖t‖ ^ 2 + ‖K q‖ ^ 2) * ‖P t‖ ^ 2 := by
    rw [← hnKu]
    nlinarith [mul_le_mul hov hov (sq_nonneg ‖t‖) (by positivity)]
  have herror : 1 - Δ * δ / (1 - δ + Δ * δ) =
      1 / (1 + Δ * δ / (1 - δ)) := by
    field_simp
    ring
  rw [herror]
  rcases eq_or_lt_of_le (sq_nonneg ‖t‖) with hx | hx
  · rw [← hx, mul_zero]
    positivity
  · have hcoef : 0 < 1 + Δ * δ / (1 - δ) := by positivity
    have hbound : ‖t‖ ^ 2 * ‖t‖ ^ 2 ≤
        ((1 + Δ * δ / (1 - δ)) * ‖t‖ ^ 2) * ‖P t‖ ^ 2 := by
      calc
        _ ≤ (‖t‖ ^ 2 + ‖K q‖ ^ 2) * ‖P t‖ ^ 2 := hsq
        _ ≤ _ := by gcongr; nlinarith [hy]
    rw [one_div_mul_eq_div, div_le_iff₀ hcoef]
    nlinarith

/-- Sharp error reduction for a single target. This is the coincident-cutoff case of
the normalized projection argument refining ALVV, arXiv:1602.08828v2, Lemma `l:er`,
lines 597–622. -/
theorem IsCloseTo.map_of_contract_sharp {δ Δ : ℝ} {U T : Submodule 𝕜 E}
    (K : E →L[𝕜] E) (h : IsCloseTo δ U T) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hΔ : 0 ≤ Δ) (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ q ∈ Tᗮ, K q ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ q ∈ Tᗮ, ‖K q‖ ^ 2 ≤ Δ * ‖q‖ ^ 2) :
    IsCloseTo (Δ * δ / (1 - δ + Δ * δ)) (U.map K.toLinearMap) T := by
  exact h.map_of_nested_contract_sharp K le_rfl hδ0 hδ hΔ hKT hKTo hlow hhigh

end Submodule
