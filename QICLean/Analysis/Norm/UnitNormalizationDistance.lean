/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Distance after normalization near a unit vector

The existing generic normed-space estimate is moved unchanged from
`TNLean/MPS/AreaLaw/MPSApproximation.lean`. It requires no Hamiltonian or
matrix product state hypothesis. This permits sequential approximations
to reuse the elementary normalization bound without importing an area law.
-/

/-- Normalizing a nonzero vector at most doubles its distance to a unit vector:
`‖Φ / ‖Φ‖ - ψ‖ ≤ |1 - ‖Φ‖| + ‖Φ - ψ‖ ≤ 2 ‖Φ - ψ‖`. -/
theorem norm_inv_norm_smul_sub_le_two_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ψ Φ : E} (hψ : ‖ψ‖ = 1) (hΦ : Φ ≠ 0) :
    ‖(‖Φ‖ : ℂ)⁻¹ • Φ - ψ‖ ≤ 2 * ‖Φ - ψ‖ := by
  have hpos : 0 < ‖Φ‖ := norm_pos_iff.mpr hΦ
  have hdiff : ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Φ‖ = |1 - ‖Φ‖| := by
    have hs : (‖Φ‖ : ℂ)⁻¹ • Φ - Φ = ((‖Φ‖⁻¹ - 1 : ℝ) : ℂ) • Φ := by
      simp [sub_smul]
    rw [hs, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      ← abs_of_nonneg (norm_nonneg Φ), ← abs_mul]
    congr 1
    rw [abs_of_nonneg (norm_nonneg Φ)]
    field_simp
  have hle : |1 - ‖Φ‖| ≤ ‖Φ - ψ‖ := by
    have h := abs_norm_sub_norm_le ψ Φ
    rwa [hψ, norm_sub_rev] at h
  calc ‖(‖Φ‖ : ℂ)⁻¹ • Φ - ψ‖ ≤ ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Φ‖ + ‖Φ - ψ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖Φ - ψ‖ := by rw [hdiff]; linarith
