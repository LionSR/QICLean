/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GapPerturbation

/-!
# Energy bound from overlap with an eigenvector

For a bounded symmetric operator `B`, a unit eigenvector `Ω` of real eigenvalue `e`, and a
unit vector `v`, the excess expectation is at most
`‖B - e • 1‖ (1 - |⟨Ω, v⟩|²)`. An overlap of at least `1 - δ` therefore gives excess at most
`2 ‖B - e • 1‖ δ`. No ground-state or finite-dimensional hypothesis is needed.

This is an auxiliary estimate for the first energy inference in the proof of Lemma
`l:within` of Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 509–515.

**Local fix (witness energy):** The source uses an unsquared overlap tolerance but omits
the resulting factor of two in that inference. The correction is recorded in
`docs/paper-gaps/lvv13_witness_energy.tex`. This auxiliary result does not prove Lemma
`l:within` or its trimming step.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {B : E →L[ℂ] E} {Ω v : E} {e M : ℝ}

/-- An upper bound on the shifted operator norm bounds the excess expectation by the
squared overlap defect. This supplies the auxiliary energy estimate for LVV,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:within`, lines 509–515. -/
theorem re_inner_sub_eigenvalue_le_of_norm_sub_le (hB : (B : E →ₗ[ℂ] E).IsSymmetric)
    (hΩ : ‖Ω‖ = 1) (hv : ‖v‖ = 1) (heig : B Ω = (e : ℂ) • Ω)
    (hM : ‖B - (e : ℂ) • ContinuousLinearMap.id ℂ E‖ ≤ M) :
    (⟪v, B v⟫_ℂ).re - e ≤ M * (1 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) := by
  let a := ⟪Ω, v⟫_ℂ
  let w := v - a • Ω
  have hΩΩ : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; simp
  have hw : ⟪Ω, w⟫_ℂ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hΩΩ, mul_one, a, sub_self]
  have hvsplit : v = a • Ω + w := by dsimp [w]; abel
  have hn : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖w‖ ^ 2 := by
    have hi : ⟪a • Ω, w⟫_ℂ = 0 := by rw [inner_smul_left, hw, mul_zero]
    conv_lhs => rw [hvsplit]
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi, norm_smul, hΩ]
    ring
  have hw2 : ‖w‖ ^ 2 = 1 - ‖a‖ ^ 2 := by rw [hv] at hn; linarith
  have hq : (⟪v, B v⟫_ℂ).re = ‖a‖ ^ 2 * e + (⟪w, B w⟫_ℂ).re := by
    conv_lhs => rw [hvsplit]
    exact re_inner_smul_add_eigenvector hB hΩ heig hw a
  let K := B - (e : ℂ) • ContinuousLinearMap.id ℂ E
  have hshift : (⟪w, K w⟫_ℂ).re = (⟪w, B w⟫_ℂ).re - e * ‖w‖ ^ 2 := by
    simp only [K, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
      Complex.re_ofReal_mul]
    rw [show (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) w]
  calc (⟪v, B v⟫_ℂ).re - e = (⟪w, K w⟫_ℂ).re := by rw [hq, hshift, hw2]; ring
    _ ≤ ‖⟪w, K w⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖w‖ * ‖K w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖K‖ * ‖w‖) := mul_le_mul_of_nonneg_left (K.le_opNorm w) (norm_nonneg _)
    _ ≤ ‖w‖ * (M * ‖w‖) := by gcongr
    _ = M * (1 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) := by rw [← hw2]; ring

/-- Unsquared overlap at least `1 - δ` gives excess expectation at most `2 M δ`.
This is the corrected auxiliary energy inference in LVV, arXiv:1307.5143v1,
`algo53.tex`, proof of Lemma `l:within`, lines 509–515. -/
theorem re_inner_sub_eigenvalue_le_of_overlap (hB : (B : E →ₗ[ℂ] E).IsSymmetric)
    (hΩ : ‖Ω‖ = 1) (hv : ‖v‖ = 1) (heig : B Ω = (e : ℂ) • Ω)
    (hM : ‖B - (e : ℂ) • ContinuousLinearMap.id ℂ E‖ ≤ M)
    {δ : ℝ} (hover : 1 - δ ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, B v⟫_ℂ).re - e ≤ 2 * M * δ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hdefect : 1 - ‖⟪Ω, v⟫_ℂ‖ ^ 2 ≤ 2 * δ := by
    nlinarith only [hover, sq_nonneg (1 - ‖⟪Ω, v⟫_ℂ‖)]
  calc (⟪v, B v⟫_ℂ).re - e ≤ M * (1 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) :=
      hB.re_inner_sub_eigenvalue_le_of_norm_sub_le hΩ hv heig hM
    _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left hdefect hM0
    _ = 2 * M * δ := by ring

end LinearMap.IsSymmetric
