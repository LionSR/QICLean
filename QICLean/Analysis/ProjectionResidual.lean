/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DetectabilityLemma

/-!
# A squared residual bound for an orthogonal projection

Pythagoras separates the component outside the projection range from the
projected input error. This estimate supports the regional frustration-free
truncation argument of ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1550.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- An orthogonal projection separates its discarded component from a projected
input error. No condition on the second vector is required. This is used in
ALVV's regional converse estimate, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1550. -/
theorem IsStarProjection.norm_sub_apply_sq_le {P : E →L[𝕜] E}
    (hP : IsStarProjection P) (x y : E) :
    ‖x - P y‖ ^ 2 ≤ ‖x - P x‖ ^ 2 + ‖x - y‖ ^ 2 := by
  have horth : ⟪x - P x, P (x - y)⟫_𝕜 = 0 := by
    rw [inner_sub_left, IsStarProjection.inner_apply_left hP,
      IsStarProjection.apply_apply_self hP, sub_self]
  have hv : x - P y = (x - P x) + P (x - y) := by
    simpa only [map_sub] using (sub_add_sub_cancel x (P x) (P y)).symm
  have hsplit : ‖x - P y‖ ^ 2 = ‖x - P x‖ ^ 2 + ‖P (x - y)‖ ^ 2 := by
    simpa only [hv, sq] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  exact hsplit.le.trans (add_le_add le_rfl
    (pow_le_pow_left₀ (norm_nonneg _) (IsStarProjection.norm_apply_le hP (x - y)) 2))

end ContinuousLinearMap
