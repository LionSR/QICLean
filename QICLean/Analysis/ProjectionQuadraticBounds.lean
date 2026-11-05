/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Projection loss and quadratic-form norm bounds

Pythagoras converts closeness into a squared projection-error bound.
Cauchy--Schwarz controls a bounded operator's quadratic form by its norm.
These estimates are shared by projected trial energy and regional-energy
arguments in ALVV, arXiv:1602.08828v2, Lemma `l:close`, lines 484–489,
and Figure `fig:algo1`, lines 1631–1632.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A bounded operator's real quadratic form is controlled by any upper
bound for its operator norm. This is the Cauchy--Schwarz estimate used
in ALVV's energy-estimation step, arXiv:1602.08828v2, line 1631. -/
theorem re_inner_apply_le_mul_norm_sq (H : E →L[𝕜] E) {A : ℝ}
    (hA : ‖H‖ ≤ A) (x : E) : RCLike.re ⟪H x, x⟫_𝕜 ≤ A * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖H x‖ * ‖x‖ := re_inner_le_norm _ _
    _ ≤ (A * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        ((H.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))) (norm_nonneg x)
    _ = _ := by ring

end ContinuousLinearMap

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Closeness bounds the squared distance to the actual orthogonal projection.
No supplied approximating vector or nonzero-target premise is needed.
Auxiliary to ALVV, arXiv:1602.08828v2, Lemma `l:close`, lines 484–489. -/
theorem IsCloseTo.norm_sub_starProjection_sq_le {delta : ℝ}
    {S T : Submodule 𝕜 E} (h : IsCloseTo delta S T) {x : E} (hx : x ∈ T) :
    ‖x - S.starProjection x‖ ^ 2 ≤ delta * ‖x‖ ^ 2 := by
  have hp := norm_sq_eq_add_norm_sq_starProjection x S
  rw [starProjection_orthogonal_val] at hp
  nlinarith only [hp, (isCloseTo_iff.mp h) x hx]

end Submodule
