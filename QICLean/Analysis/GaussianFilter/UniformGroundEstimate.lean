/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.GroundEstimate
import QICLean.Analysis.GaussianFilter.ParameterChoice

/-!
# Uniform bounds for the truncated Gaussian ground-vector filter

For each positive gap `Δ` and nonnegative real exponent `r`, choose constants
`A > 0` and `T₀ > 0` before the buffer parameter, system size, finite coordinate type,
and matrix data.
The actual unrenormalized Gaussian filter with variance `A * (1 + b + log L)`
and cutoff `T₀ * (1 + b + log L)` is a contraction whenever its input is a
contraction. Both ground-vector residuals are bounded by
`3 * exp (-10 * b) * L ^ (-r)`. The adjoint residual has the conjugate overlap.

The factor `3` is the sum of the scalar spectral factor `1` and truncation
factor `2`. The proof composes `exists_gaussian_parameters` with the actual
integral estimates; it assumes neither the residual bounds nor an operator
existence conclusion. The real variance is positive, and its conversion to
`ℝ≥0` is accompanied by an exact equality.

Source: polynomial-PEPS manuscript (2026), `lem:reset`, `02-information.tex`,
lines 443–452, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the uniform Gaussian approximation step only. No spatial locality or
full reset conclusion is asserted. No OpenAI Lean proof text is copied or adapted.
-/

/-
Provenance-ID: gaussian8766-uniform-truncated-ground
Downstream declaration: GaussianFilter.exists_uniform_truncated_ground_estimate
Source: peps-02-information-adc7f124.tex, lines 443–452.
Reuse: local scalar parameter choice, actual two-sided truncated integral estimate,
and the local unrenormalized integral contraction bound.
-/

open Complex Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal ComplexOrder

namespace GaussianFilter

universe u

/-- Fixed Gaussian parameters give an actual truncated contraction and two
ground-vector errors with explicit factor `3`, as in `02-information.tex`,
`lem:reset`, lines 443–452. The constants precede all scale and matrix data.
The reverse coefficient is the conjugate overlap, without a reality assumption. -/
theorem exists_uniform_truncated_ground_estimate {Δ r : ℝ}
    (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      ∀ b L : ℝ, 0 ≤ b → 1 ≤ L →
        let B := 1 + b + Real.log L
        let h := Real.toNNReal (A * B)
        let T := T₀ * B
        (h : ℝ) = A * B ∧ 0 < (h : ℝ) ∧ 0 ≤ T ∧
          ∀ (n : Type u) [Fintype n] [DecidableEq n],
          ∀ H' H W : Matrix n n ℂ, H'.IsHermitian → H.IsHermitian → ‖W‖ ≤ 1 →
            ∀ (E₀ : ℝ) (Ψ Φ : EuclideanSpace ℂ n), ‖Ψ‖ = 1 → ‖Φ‖ = 1 →
              H *ᵥ WithLp.ofLp Ψ = (E₀ : ℂ) • WithLp.ofLp Ψ →
              H' *ᵥ WithLp.ofLp Φ = (E₀ : ℂ) • WithLp.ofLp Φ →
              (H - (E₀ : ℂ) • 1 - (Δ : ℂ) •
                (1 - vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ)))).PosSemidef →
              (H' - (E₀ : ℂ) • 1 - (Δ : ℂ) •
                (1 - vecMulVec (WithLp.ofLp Φ) (star (WithLp.ofLp Φ)))).PosSemidef →
              let M := gaussianIntertwinerTruncated h T H' H W
              let z := ⟪Φ, toEuclideanLin W Ψ⟫_ℂ
              ‖M‖ ≤ 1 ∧
                ‖toEuclideanLin M Ψ - z • Φ‖ ≤ 3 * Real.exp (-10 * b) * L ^ (-r) ∧
                ‖toEuclideanLin Mᴴ Φ - star z • Ψ‖ ≤
                  3 * Real.exp (-10 * b) * L ^ (-r) := by
  obtain ⟨A, T₀, hA, hT₀, _, _, hscale⟩ := exists_gaussian_parameters hΔ hr
  refine ⟨A, T₀, hA, hT₀, ?_⟩
  intro b L hb hL
  let B := 1 + b + Real.log L
  let h := Real.toNNReal (A * B)
  let T := T₀ * B
  have hscalar := hscale b L hb hL
  have hh : (h : ℝ) = A * B := Real.coe_toNNReal _ hscalar.1.le
  refine ⟨hh, ?_, hscalar.2.1, ?_⟩
  · rw [hh]
    exact hscalar.1
  intro n _ _ H' H W hH' hH hW E₀ Ψ Φ hΨ hΦ hHΨ hH'Φ hgap hgap'
  obtain ⟨hforward, hreverse⟩ := gaussianIntertwinerTruncated_two_sided_ground_estimate
    h hscalar.2.1 hH' hH W hΨ hΦ hHΨ hH'Φ hgap hgap' hΔ
  have hsum : Real.exp (-(h : ℝ) * Δ ^ 2 / 2) +
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) ≤
        3 * Real.exp (-10 * b) * L ^ (-r) := by
    rw [hh]
    nlinarith only [hscalar.2.2.1, hscalar.2.2.2]
  have hnonneg : 0 ≤ Real.exp (-(h : ℝ) * Δ ^ 2 / 2) +
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) := by positivity
  have hbound := (mul_le_of_le_one_right hnonneg hW).trans hsum
  exact ⟨(norm_gaussianIntertwinerTruncated_le h T hH' hH W).trans hW,
    hforward.trans hbound, hreverse.trans hbound⟩

end GaussianFilter
