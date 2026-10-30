/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Squared triangle inequality in a seminormed additive group

The square of a distance is at most twice the sum of the two squared
successive distances. This elementary inequality is used when comparing
changing spectral targets in AKLV, arXiv:1301.1162v1, Lemma `l:5`,
lines 1025--1052.
-/

/-- The squared triangle inequality with factor two. -/
theorem norm_sub_sq_le_two_mul_add {F : Type*} [SeminormedAddCommGroup F]
    (x y z : F) : ‖x - z‖ ^ 2 ≤ 2 * (‖x - y‖ ^ 2 + ‖y - z‖ ^ 2) := by
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (norm_sub_le_norm_sub_add_norm_sub x y z) 2).trans add_sq_le
