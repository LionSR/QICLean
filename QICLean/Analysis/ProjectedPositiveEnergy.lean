/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectionQuadraticBounds
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive energy after projection into a close space

The regional energy-estimation step in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1631–1632, and proof of `t:alg1`, lines 1805–1806,
uses a low-energy vector projected into a viable space. A positive regional
operator need not annihilate the original global ground space. Its original
quadratic-form bound and the projection loss still give an explicit energy
bound. The estimates below concern the actual orthogonal projection.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A weighted bound for a positive quadratic form at a sum. It follows
by evaluating the form at the difference with the second vector multiplied
by a positive real weight. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1631–1632. -/
theorem IsPositive.re_inner_add_le_weighted {H : E →L[𝕜] E}
    (hH : H.IsPositive) (x y : E) {r : ℝ} (hr : 0 < r) :
    RCLike.re ⟪H (x + y), x + y⟫_𝕜 ≤
      (1 + 1 / r) * RCLike.re ⟪H x, x⟫_𝕜 +
        (1 + r) * RCLike.re ⟪H y, y⟫_𝕜 := by
  have hdiff := hH.re_inner_nonneg_left (x - (r : 𝕜) • y)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul] at hdiff
  calc
    _ ≤ ((r + 1) * RCLike.re ⟪H x, x⟫_𝕜 +
        r * (r + 1) * RCLike.re ⟪H y, y⟫_𝕜) / r := by
      apply (le_div_iff₀ hr).mpr
      simp only [map_add, inner_add_left, inner_add_right]
      nlinarith only [hdiff]
    _ = _ := by field_simp [hr.ne']; ring

end ContinuousLinearMap

namespace Real

/-- A small projection loss keeps a regional energy initially at most two
below three after normalization. This is a numerical auxiliary for ALVV,
arXiv:1602.08828v2, the energy-estimation step in Figure `fig:algo1`,
lines 1631–1632. -/
theorem projected_positive_energy_le_three {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (100 * (A + 1))) :
    δ < 1 ∧ (9 / 4 + 9 * A * δ) / (1 - δ) ≤ 3 := by
  have hmul : δ * (100 * (A + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 100 * (A + 1))).mp hsmall
  have hδ1 : δ < 1 := by nlinarith only [hmul, mul_nonneg hA hδ]
  refine ⟨hδ1, (div_le_iff₀ (by linarith only [hδ1] : 0 < 1 - δ)).mpr ?_⟩
  nlinarith only [hmul, hδ, mul_nonneg hA hδ]

end Real

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The actual projected target space has bounded positive energy when the
original target has bounded positive energy. In contrast to the zero-energy
case, the regional operator need not annihilate the global ground space.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632,
and proof of `t:alg1`, lines 1805–1806. -/
theorem IsCloseTo.map_starProjection_positive_energy_le {δ E0 A : ℝ}
    {U G : Submodule 𝕜 E} (h : IsCloseTo δ U G) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (r : ℝ) (hr : 0 < r) (H : E →L[𝕜] E) (hH : H.IsPositive) (hE0 : 0 ≤ E0)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ E0 * ‖g‖ ^ 2) (hA : ‖H‖ ≤ A) :
    ∀ x ∈ G.map U.starProjection.toLinearMap,
      RCLike.re ⟪H x, x⟫_𝕜 ≤ ((1 + 1 / r) * E0 + (1 + r) * A * δ) / (1 - δ) * ‖x‖ ^ 2 := by
  rintro x ⟨g, hg, rfl⟩
  change RCLike.re ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 ≤
    ((1 + 1 / r) * E0 + (1 + r) * A * δ) / (1 - δ) * ‖U.starProjection g‖ ^ 2
  have hc : 0 < 1 - δ := by linarith only [hδ]
  have hA0 : 0 ≤ A := (norm_nonneg H).trans hA
  have hlow := (isCloseTo_iff.mp h) g hg
  have hdist : ‖U.starProjection g - g‖ ^ 2 ≤ δ * ‖g‖ ^ 2 := by
    simpa only [norm_sub_rev] using h.norm_sub_starProjection_sq_le hg
  have hdiffEnergy : RCLike.re ⟪H (U.starProjection g - g), U.starProjection g - g⟫_𝕜 ≤
      A * δ * ‖g‖ ^ 2 := by
    calc
      _ ≤ A * ‖U.starProjection g - g‖ ^ 2 :=
        H.re_inner_apply_le_mul_norm_sq hA _
      _ ≤ A * (δ * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_left hdist hA0
      _ = _ := by ring
  have henergy : RCLike.re ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 ≤
      ((1 + 1 / r) * E0 + (1 + r) * A * δ) * ‖g‖ ^ 2 := by
    calc
      _ ≤ (1 + 1 / r) * RCLike.re ⟪H g, g⟫_𝕜 +
          (1 + r) * RCLike.re ⟪H (U.starProjection g - g), U.starProjection g - g⟫_𝕜 := by
        simpa only [add_sub_cancel] using
          hH.re_inner_add_le_weighted g (U.starProjection g - g) hr
      _ ≤ (1 + 1 / r) * (E0 * ‖g‖ ^ 2) + (1 + r) * (A * δ * ‖g‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hG g hg) (by positivity))
          (mul_le_mul_of_nonneg_left hdiffEnergy (by positivity))
      _ = _ := by ring
  have hnorm : ‖g‖ ^ 2 ≤ ‖U.starProjection g‖ ^ 2 / (1 - δ) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlow)
  calc
    _ ≤ ((1 + 1 / r) * E0 + (1 + r) * A * δ) * ‖g‖ ^ 2 := henergy
    _ ≤ ((1 + 1 / r) * E0 + (1 + r) * A * δ) * (‖U.starProjection g‖ ^ 2 / (1 - δ)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- A candidate with projection loss at most the displayed inverse-norm
scale has regional energy at most three on the actual projected target
space, provided the original regional energy is at most two. This is an
auxiliary for ALVV, arXiv:1602.08828v2, the energy-estimation step in
Figure `fig:algo1`, lines 1631–1632. -/
theorem IsCloseTo.map_starProjection_energy_le_three {δ A : ℝ}
    {U G : Submodule 𝕜 E} (h : IsCloseTo δ U G) (hδ0 : 0 ≤ δ)
    (H : E →L[𝕜] E) (hH : H.IsPositive)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ 2 * ‖g‖ ^ 2)
    (hA : ‖H‖ ≤ A) (hsmall : δ ≤ 1 / (100 * (A + 1))) :
    ∀ x ∈ G.map U.starProjection.toLinearMap,
      RCLike.re ⟪H x, x⟫_𝕜 ≤ 3 * ‖x‖ ^ 2 := by
  have hnum := Real.projected_positive_energy_le_three ((norm_nonneg H).trans hA) hδ0 hsmall
  have hraw := h.map_starProjection_positive_energy_le hδ0 hnum.1 8 (by norm_num)
    H hH (by norm_num) hG hA
  norm_num only at hraw
  intro x hx
  exact (hraw x hx).trans (mul_le_mul_of_nonneg_right hnum.2 (sq_nonneg ‖x‖))

end Submodule
