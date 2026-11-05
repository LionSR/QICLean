/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectionQuadraticBounds
import QICLean.Analysis.ViableProjectionNonzero
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# The energy of a projected trial space

For the final spectral extraction in ALVV, arXiv:1602.08828v2,
Algorithm `t:alg1`, lines 1634–1640, a candidate space close to the full
ground space must supply a trial space of the same dimension. Projecting
the ground space into the candidate constructs that trial space directly.
The energy bound holds on its entire span.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Projecting a zero-energy target into a close candidate gives an actual trial
space of the same dimension, with a bound on every vector's energy. This is an
auxiliary for the compressed spectral extraction in ALVV, arXiv:1602.08828v2,
Algorithm `t:alg1`, lines 1634–1640. -/
theorem IsCloseTo.map_starProjection_energy_le {δ A : ℝ} {U G : Submodule 𝕜 E}
    (h : IsCloseTo δ U G) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (H : E →L[𝕜] E) (hH : H.toLinearMap.IsSymmetric)
    (hG : ∀ g ∈ G, H g = 0) (hA : ‖H‖ ≤ A) :
    G.map U.starProjection.toLinearMap ≤ U ∧
      Module.finrank 𝕜 (G.map U.starProjection.toLinearMap) = Module.finrank 𝕜 G ∧
      ∀ x ∈ G.map U.starProjection.toLinearMap,
        RCLike.re ⟪H x, x⟫_𝕜 ≤ A * δ / (1 - δ) * ‖x‖ ^ 2 := by
  have hc : 0 < 1 - δ := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg H).trans hA
  have hv := isCloseTo_iff.mp h
  let f : G →ₗ[𝕜] E := U.starProjection.toLinearMap.comp G.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    by_contra hne
    exact (h.starProjection_ne_zero hδ g.2 hne) hg
  have hupper (v : E) : RCLike.re ⟪H v, v⟫_𝕜 ≤ A * ‖v‖ ^ 2 :=
    H.re_inner_apply_le_mul_norm_sq hA v
  have hrange : f.range = G.map U.starProjection.toLinearMap := by
    change (U.starProjection.toLinearMap.comp G.subtype).range = _
    rw [LinearMap.range_comp, G.range_subtype]
  have hdim : Module.finrank 𝕜 (G.map U.starProjection.toLinearMap) = Module.finrank 𝕜 G :=
    (congrArg (fun P : Submodule 𝕜 E => Module.finrank 𝕜 P) hrange).symm.trans
      (LinearMap.finrank_range_of_inj hinj)
  simp only [← hrange]
  refine ⟨?_, hdim, ?_⟩
  · rintro x ⟨g, rfl⟩
    exact U.starProjection_apply_mem g
  · rintro x ⟨g, rfl⟩
    change RCLike.re ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 ≤ _
    have hlow := hv g g.2
    have hdist : ‖U.starProjection (g : E) - g‖ ^ 2 ≤ δ * ‖(g : E)‖ ^ 2 := by
      simpa only [norm_sub_rev] using h.norm_sub_starProjection_sq_le g.2
    have hdiff : ‖U.starProjection (g : E) - g‖ ^ 2 ≤
        δ / (1 - δ) * ‖U.starProjection (g : E)‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have hh := mul_le_mul_of_nonneg_right hdist hc.le
      have hl := mul_le_mul_of_nonneg_left hlow hδ0
      nlinarith
    have hzero : H (g : E) = 0 := hG g g.2
    have hcross : ⟪H (U.starProjection g), (g : E)⟫_𝕜 = 0 := by
      calc
        _ = ⟪U.starProjection g, H (g : E)⟫_𝕜 := hH _ _
        _ = 0 := by rw [hzero, inner_zero_right]
    have heq : ⟪H (U.starProjection (g : E) - g), U.starProjection (g : E) - g⟫_𝕜 =
        ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 := by
      rw [map_sub, hzero, sub_zero, inner_sub_right, hcross, sub_zero]
    calc
      _ = RCLike.re ⟪H (U.starProjection (g : E) - g), U.starProjection (g : E) - g⟫_𝕜 :=
        congrArg RCLike.re heq.symm
      _ ≤ A * ‖U.starProjection (g : E) - g‖ ^ 2 := hupper _
      _ ≤ A * (δ / (1 - δ) * ‖U.starProjection (g : E)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff hA0
      _ = _ := by dsimp [f]; ring

end Submodule
