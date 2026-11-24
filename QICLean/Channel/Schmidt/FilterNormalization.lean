/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Schmidt.ProductOverlapBootstrap
import QICLean.Spectral.Filter.PhaseNormalization

/-!
# Schmidt rank of a phase-aligned filtered vector

The normalized output of a bipartite filter has Schmidt rank at most the
operator Schmidt rank of the filter times the Schmidt rank of the input.
The spectral estimate also bounds its distance to the target vector up to
a unit phase.
-/

open scoped InnerProductSpace

namespace Matrix

/-- Phase alignment and normalization preserve the rank bound of the actual
filtered image. AKLV, arXiv:1301.1162v1, Definition `def:AGSP` and the
normalized filtering steps of Lemma `l:5`, lines 1023--1048. -/
theorem exists_phase_normalized_filter_output_of_operatorSchmidtRank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ) (Γ x : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hfix : toEuclideanLin K Γ = Γ) (δ : ℝ)
    (hperp : ∀ v : EuclideanSpace ℂ (m × n), ‖v‖ = 1 → ⟪Γ, v⟫_ℂ = 0 →
      ⟪Γ, toEuclideanLin K v⟫_ℂ = 0 ∧ ‖toEuclideanLin K v‖ ^ 2 ≤ δ)
    (hoverlap : ⟪Γ, x⟫_ℂ ≠ 0) :
    toEuclideanLin K x ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
      let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
      ‖ψ‖ = 1 ∧
        schmidtRank (WithLp.ofLp ψ) ≤ operatorSchmidtRank K * schmidtRank (WithLp.ofLp x) ∧
        ‖ψ - Γ‖ ^ 2 ≤
          2 * δ * ‖x - ⟪Γ, x⟫_ℂ • Γ‖ ^ 2 / ‖⟪Γ, x⟫_ℂ‖ ^ 2 := by
  obtain ⟨hy0, c, hc, hunit, herror⟩ :=
    exists_phase_normalized_filter_output K Γ x hΓ hfix δ hperp hoverlap
  refine ⟨hy0, c, hc, hunit, ?_, herror⟩
  simp only [WithLp.ofLp_smul]
  rw [schmidtRank_smul_eq_of_ne_zero c (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hc),
    schmidtRank_smul_eq_of_ne_zero _ (by exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hy0))]
  exact schmidtRank_mulVec_le K (WithLp.ofLp x)

end Matrix
