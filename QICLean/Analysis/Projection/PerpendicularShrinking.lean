/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Extending a bound from the unit sphere in an orthogonal complement

A linear map that preserves the orthogonal complement of `Γ` on unit vectors
preserves it everywhere. Any uniform squared-norm bound on those unit vectors
extends by homogeneity.
-/

open scoped InnerProductSpace

namespace Matrix

/-- A contraction bound on unit perpendicular vectors extends homogeneously,
without any sign assumption on the squared-norm bound. -/
theorem perpendicular_shrinking_homogeneous
    {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Γ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hperp : ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
      ⟪Γ, A ψ⟫_ℂ = 0 ∧ ‖A ψ‖ ^ 2 ≤ δ)
    (v : EuclideanSpace ℂ ι) (hv : ⟪Γ, v⟫_ℂ = 0) :
    ⟪Γ, A v⟫_ℂ = 0 ∧ ‖A v‖ ^ 2 ≤ δ * ‖v‖ ^ 2 := by
  by_cases hz : v = 0
  · simp only [hz, map_zero, inner_zero_right, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl, and_self]
  · let y := NormedSpace.normalize v
    have hy : ‖y‖ = 1 := NormedSpace.norm_normalize hz
    have hscale : v = (‖v‖ : ℂ) • y := by
      calc
        v = ‖v‖ • y := (NormedSpace.norm_smul_normalize v).symm
        _ = (‖v‖ : ℂ) • y := RCLike.real_smul_eq_coe_smul (K := ℂ) ‖v‖ y
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    have hyorth : ⟪Γ, y⟫_ℂ = 0 := by
      have hh : (‖v‖ : ℂ) * ⟪Γ, y⟫_ℂ = 0 := by
        have hh := hv
        rw [hscale, inner_smul_right] at hh
        exact hh
      exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hn.ne')
    obtain ⟨hortho, hnorm⟩ := hperp y hy hyorth
    have hAv : A v = (‖v‖ : ℂ) • A y := by
      conv_lhs => rw [hscale, map_smul]
    constructor
    · rw [hAv, inner_smul_right, hortho, mul_zero]
    · calc
        ‖A v‖ ^ 2 = ‖v‖ ^ 2 * ‖A y‖ ^ 2 := by
          rw [hAv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hn, mul_pow]
        _ ≤ ‖v‖ ^ 2 * δ := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
        _ = δ * ‖v‖ ^ 2 := mul_comm _ _

end Matrix
