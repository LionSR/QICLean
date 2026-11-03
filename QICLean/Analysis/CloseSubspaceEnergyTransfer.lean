/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectedPositiveEnergy

/-!
# Positive energy on a nearby target space

A positive regional operator need not vanish on the original global ground
space. Its quadratic-form bound transfers to a nearby soft spectral space
by projecting the latter into the original space. The projection loss and
operator norm remain explicit. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisefficient`, lines 1360–1371, and the energy-estimation
argument in the proof of `t:alg1`, line 1807.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A bound for a positive quadratic form transfers from a subspace to a
nearby target. The actual projection into the first space supplies the
comparison vector; no approximating vector is assumed.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:aisefficient`,
lines 1360–1371, and the energy-estimation argument at line 1807. -/
theorem IsCloseTo.positive_energy_le {delta E0 A : ℝ}
    {G T : Submodule 𝕜 E} (h : IsCloseTo delta G T)
    (H : E →L[𝕜] E) (hH : H.IsPositive) (hE0 : 0 ≤ E0)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ E0 * ‖g‖ ^ 2) (hA : ‖H‖ ≤ A)
    (r : ℝ) (hr : 0 < r) :
    ∀ t ∈ T, RCLike.re ⟪H t, t⟫_𝕜 ≤
      ((1 + 1 / r) * E0 + (1 + r) * A * delta) * ‖t‖ ^ 2 := by
  intro t ht
  have hprojected : RCLike.re ⟪H (G.starProjection t), G.starProjection t⟫_𝕜 ≤
      E0 * ‖t‖ ^ 2 :=
    (hG _ (G.starProjection_apply_mem t)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (G.norm_starProjection_apply_le t) 2) hE0)
  have hdiff : RCLike.re ⟪H (t - G.starProjection t), t - G.starProjection t⟫_𝕜 ≤
      A * delta * ‖t‖ ^ 2 := by
    calc
      _ ≤ A * ‖t - G.starProjection t‖ ^ 2 := H.re_inner_apply_le_mul_norm_sq hA _
      _ ≤ A * (delta * ‖t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h.norm_sub_starProjection_sq_le ht)
          ((norm_nonneg H).trans hA)
      _ = _ := by ring
  calc
    _ ≤ (1 + 1 / r) * RCLike.re ⟪H (G.starProjection t), G.starProjection t⟫_𝕜 +
        (1 + r) * RCLike.re ⟪H (t - G.starProjection t), t - G.starProjection t⟫_𝕜 := by
      simpa only [add_sub_cancel] using
        hH.re_inner_add_le_weighted (G.starProjection t) (t - G.starProjection t) hr
    _ ≤ (1 + 1 / r) * (E0 * ‖t‖ ^ 2) + (1 + r) * (A * delta * ‖t‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hprojected (by positivity))
        (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring

end Submodule
