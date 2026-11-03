/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Nonzero projections from a close target

A closeness loss below one makes the orthogonal projection injective on
its target. In particular, projecting a nonzero target vector gives a
nonzero candidate vector. This is a finite-dimensional consequence of
ALVV, arXiv:1602.08828v2, the vector characterization of closeness at
line 488, used for the trial vectors in lines 1631 and 1807.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Loss below one preserves nonzero vectors under the actual projection.
Auxiliary to ALVV, arXiv:1602.08828v2, the vector characterization of
closeness at line 488 and the trial-vector step at line 1807. -/
theorem IsCloseTo.starProjection_ne_zero {delta : ℝ} {U T : Submodule 𝕜 E}
    (h : IsCloseTo delta U T) (hdelta : delta < 1) {t : E}
    (ht : t ∈ T) (htne : t ≠ 0) : U.starProjection t ≠ 0 := by
  intro hz
  have hh := (isCloseTo_iff.mp h) t ht
  rw [hz, norm_zero, zero_pow two_ne_zero] at hh
  have hp : 0 < (1 - delta) * ‖t‖ ^ 2 :=
    mul_pos (sub_pos.mpr hdelta) (sq_pos_of_pos (norm_pos_iff.mpr htne))
  exact (not_lt_of_ge hh) hp

end Submodule
