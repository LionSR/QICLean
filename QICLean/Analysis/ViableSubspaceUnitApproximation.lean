/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Normalized projections from close subspaces

For a unit vector in the target of a close subspace, its orthogonal projection
is nonzero. Normalizing that projection preserves the squared-overlap bound
and fixes the phase: the inner product with the original vector is a
nonnegative real number. The squared distance is at most twice the closeness
error. These are vector consequences of ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474.
-/

open scoped InnerProductSpace ComplexOrder

namespace Submodule

/-- A unit target vector admits its normalized orthogonal projection in the
approximating subspace. The projection has squared overlap at least `1 - δ`,
its phase is aligned with the target, and its squared distance is at most
`2 * δ`. This is the vector interpretation of ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474. -/
theorem IsCloseTo.exists_unit_mem_norm_inner_sq_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {δ : ℝ} {S T : Submodule ℂ E}
    (h : IsCloseTo δ S T) (hδ : δ < 1) {ψ : E} (hψT : ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    ∃ φ : E, φ ∈ S ∧ ‖φ‖ = 1 ∧ 1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ∧
      ⟪φ, ψ⟫_ℂ = ((‖S.starProjection ψ‖ : ℝ) : ℂ) ∧
      ‖φ - ψ‖ ^ 2 ≤ 2 * δ ∧
      φ = ((‖S.starProjection ψ‖⁻¹ : ℝ) : ℂ) • S.starProjection ψ := by
  let p := S.starProjection ψ
  have hproj : 1 - δ ≤ ‖p‖ ^ 2 := by
    simpa only [hψ, one_pow, mul_one] using isCloseTo_iff.mp h ψ hψT
  have hp : 0 < ‖p‖ := by nlinarith [norm_nonneg p]
  have hpp : ⟪p, ψ⟫_ℂ = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    have he : S.starProjection p = p :=
      S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem ψ)
    have hinner : ⟪p, ψ⟫_ℂ = ⟪p, p⟫_ℂ := by
      calc
        ⟪p, ψ⟫_ℂ = ⟪S.starProjection p, ψ⟫_ℂ := by rw [he]
        _ = ⟪p, S.starProjection ψ⟫_ℂ := S.inner_starProjection_left_eq_right _ _
    rw [hinner, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  let φ := ((‖p‖⁻¹ : ℝ) : ℂ) • p
  have hφ : ‖φ‖ = 1 := by
    dsimp only [φ]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hp,
      inv_mul_cancel₀ hp.ne']
  have hinner : ⟪φ, ψ⟫_ℂ = ((‖p‖ : ℝ) : ℂ) := by
    dsimp only [φ]
    rw [inner_smul_left, hpp, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have hoverlap : ‖⟪φ, ψ⟫_ℂ‖ = ‖p‖ := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  refine ⟨φ, S.smul_mem _ (S.starProjection_apply_mem ψ), hφ,
    by simpa only [hoverlap] using hproj, hinner, ?_, rfl⟩
  have hple : ‖p‖ ≤ 1 := by simpa only [hψ] using S.norm_starProjection_apply_le ψ
  have hsq : ‖p‖ ^ 2 ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  rw [norm_sub_sq (𝕜 := ℂ), hφ, hψ, hinner]
  change 1 ^ 2 - 2 * ‖p‖ + 1 ^ 2 ≤ 2 * δ
  nlinarith

end Submodule
