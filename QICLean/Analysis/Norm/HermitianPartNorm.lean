/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Operator norm of the Hermitian part of a matrix

The existing real-linear Hermitian-part map is a contraction in operator norm. Consequently,
replacing an approximant by its Hermitian part does not increase its distance from a Hermitian
matrix. These are finite-dimensional supporting estimates for approximate Hamiltonians in
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff` and `t:aisefficient`, lines 1262–1268 and 1412–1420.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- Taking the existing Hermitian part is contractive in operator norm. Supporting the
Hermitian approximation used with ALVV, arXiv:1602.08828v2, lines 1262–1268 and 1412–1420. -/
theorem norm_selfAdjointPart_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) : ‖(selfAdjointPart ℝ B : Matrix ι ι ℂ)‖ ≤ ‖B‖ := by
  calc
    ‖(selfAdjointPart ℝ B : Matrix ι ι ℂ)‖ = (1 / 2 : ℝ) * ‖B + star B‖ := by
      change ‖(⅟(2 : ℝ)) • (B + star B)‖ = _
      rw [norm_smul]
      norm_num [invOf_eq_inv]
    _ ≤ (1 / 2 : ℝ) * (‖B‖ + ‖star B‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le B (star B)) (by norm_num)
    _ = ‖B‖ := by rw [norm_star]; ring

/-- The Hermitian part of an approximant is no farther from a Hermitian target. Supporting
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff` and `t:aisefficient`,
lines 1262–1268 and 1412–1420. -/
theorem IsHermitian.norm_sub_selfAdjointPart_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (B : Matrix ι ι ℂ) :
    ‖H - (selfAdjointPart ℝ B : Matrix ι ι ℂ)‖ ≤ ‖H - B‖ := by
  calc
    _ = ‖(selfAdjointPart ℝ (H - B) : Matrix ι ι ℂ)‖ := by
      rw [map_sub]
      simp [hH.isSelfAdjoint.coe_selfAdjointPart_apply ℝ]
    _ ≤ _ := norm_selfAdjointPart_le (H - B)

end Matrix
