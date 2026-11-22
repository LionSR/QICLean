/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MutualInformation.PhysicalBuffer
import QICLean.Analysis.Parameter.ParameterChoice

/-!
# Uniform Gaussian approximation from one physical ground state

Fix a positive gap and a nonnegative decay exponent. Any Gaussian constants `A, T₀`
with `30 + r ≤ A Δ² / 2` and `30 + r ≤ T₀² / (2 A)` work for all finite register
types, Hamiltonians, normalized ground states, entropy bounds, and size parameters.
The physical buffer operator and its real overlap are chosen before the size parameter.
The actual truncated two-generator Gaussian integral is a contraction with both residuals bounded by
`3 * exp (-10 * b) * L ^ (-r)`.

The paired ground vectors and gaps are derived by doubling, regrouping and the
partial swap from the original-system assumptions. No regional locality or
complete reset statement is asserted.

Source: polynomial-PEPS manuscript (September 24, 2026), `lem:reset`,
`02-information.tex`, lines 395–452, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Reuse: the physical-buffer Gaussian construction and scalar parameter estimates.
No OpenAI Lean proof text is copied or adapted.
-/

open Complex Matrix
open scoped Kronecker ComplexOrder InnerProductSpace Matrix.Norms.L2Operator NNReal

namespace GaussianFilter

universe u v w

/-- **The physical-buffer filter with explicit constants.** Let `A, T₀ ≥ 0` satisfy the two
numerical conditions `30 + r ≤ A Δ² / 2` and `30 + r ≤ T₀² / (2 A)` of the manuscript. Then
the variance `A B` and the cutoff `T₀ B`, with `B = 1 + b + log L`, give an actual truncated
filter from original-system gap and entropy data, for all finite register types. The
original-buffer contraction and real overlap work simultaneously for every size parameter.
Polynomial PEPS approximation, `02-information.tex`, lines 395–452; the constants
`A = 2 (30 + r) / Δ²` and `T₀ = 2 (30 + r) / Δ` of lines 443–450 meet both conditions. -/
theorem physicalBuffer_filter_of_le {Δ r a T₀ : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) (hT₀ : 0 ≤ T₀)
    (hgap : 30 + r ≤ a * Δ ^ 2 / 2) (htail : 30 + r ≤ T₀ ^ 2 / (2 * a)) :
      ∀ (R : Type u) (C : Type v) (Q : Type w)
        [Fintype R] [Fintype C] [Fintype Q]
        [DecidableEq R] [DecidableEq C] [DecidableEq Q]
        (H : Matrix ((R × C) × Q) ((R × C) × Q) ℂ)
        (Ω : (R × C) × Q → ℂ) (E₀ b : ℝ),
        star Ω ⬝ᵥ Ω = 1 → H *ᵥ Ω = (E₀ : ℂ) • Ω →
        (H - (E₀ : ℂ) • 1 -
          (Δ : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef → 0 ≤ b →
        quantumRelativeEntropy
          (partialTraceRight (vecMulVec Ω (star Ω)))
          (partialTraceRight (partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
            partialTraceLeft (partialTraceRight (vecMulVec Ω (star Ω)))) ≤ b →
        let e := Equiv.doubledRegroup (R × C) Q
        let ψ := doubledRegroup Ω
        let φ := physicalLeftSwap ψ
        let S := partialSwap R C ⊗ₖ (1 : Matrix (Q × Q) (Q × Q) ℂ)
        let K := reindex e e (doubledHamiltonian H)
        let K' := S * K * Sᴴ
        let Ψ : EuclideanSpace ℂ _ := WithLp.toLp 2 ψ
        let Φ : EuclideanSpace ℂ _ := WithLp.toLp 2 φ
        ∃ (W : Matrix (Q × Q) (Q × Q) ℂ) (z : ℝ),
          let V := (1 : Matrix ((R × C) × (R × C)) ((R × C) × (R × C)) ℂ) ⊗ₖ W
          W.IsHermitian ∧ ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧
          star φ ⬝ᵥ (V *ᵥ ψ) = (z : ℂ) ∧
          ∀ L : ℝ, 1 ≤ L →
            let B := 1 + b + Real.log L
            let h := Real.toNNReal (a * B)
            let T := T₀ * B
            let M := gaussianIntertwinerTruncated h T K' K V
            (h : ℝ) = a * B ∧ 0 < (h : ℝ) ∧ 0 ≤ T ∧ ‖M‖ ≤ 1 ∧
              ‖toEuclideanLin M Ψ - (z : ℂ) • Φ‖ ≤
                3 * Real.exp (-10 * b) * L ^ (-r) ∧
              ‖toEuclideanLin Mᴴ Φ - (z : ℂ) • Ψ‖ ≤
                3 * Real.exp (-10 * b) * L ^ (-r) := by
  have ha : 0 < a := by
    by_contra h
    have : a * Δ ^ 2 / 2 ≤ 0 := by
      have := sq_nonneg Δ
      have : a ≤ 0 := not_lt.mp h
      nlinarith
    linarith
  intro R C Q _ _ _ _ _ _ H Ω E₀ b hΩ heigen hgapΩ hb hbound
  obtain ⟨W, z, hWherm, hW, hz, hoverlap, hfilter⟩ :=
    exists_physicalBuffer_gaussian_filter H Ω hΩ heigen hgapΩ hΔ hb hbound
  refine ⟨W, z, hWherm, hW, hz, hoverlap, ?_⟩
  intro L hL
  let B := 1 + b + Real.log L
  let h := Real.toNNReal (a * B)
  let T := T₀ * B
  have hs := gaussian_error_bounds_of_parameter_constants ha hT₀ hr hgap htail hb hL
  have hh : (h : ℝ) = a * B := Real.coe_toNNReal _ hs.1.le
  obtain ⟨hM, hforward, hreverse⟩ := (hfilter h).2.2.2 T hs.2.1
  have hsum : Real.exp (-(h : ℝ) * Δ ^ 2 / 2) +
      2 * Real.exp (-T ^ 2 / (2 * (h : ℝ))) ≤
        3 * Real.exp (-10 * b) * L ^ (-r) := by
    rw [hh]
    nlinarith only [hs.2.2.1, hs.2.2.2]
  refine ⟨hh, ?_, hs.2.1, hM, hforward.trans hsum, hreverse.trans hsum⟩
  rw [hh]
  exact hs.1

end GaussianFilter
