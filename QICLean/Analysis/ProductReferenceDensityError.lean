/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChronologicalGarbage

/-!
# Density error relative to a subnormalized product reference

Let `Ω` be a unit physical vector, `Ξ` a private vector of norm at most one,
and `Ψ` the actual joint vector. Discarding the private coordinates of
`Ω ⊗ Ξ` gives `‖Ξ‖² |Ω⟩⟨Ω|`. Consequently the physical density error of `Ψ`
is at most twice its vector error relative to `Ω ⊗ Ξ`, plus `1 - ‖Ξ‖²`,
provided `‖Ψ‖ ≤ 1`. If `‖Ξ‖ ≥ 1 - δ`, the last term is at most `2δ`.
Neither vector is renormalized, and no positive lower bound on `‖Ξ‖` is used.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
§8.1, `eq:reference-junk` and `eq:protocol-density`, `07-assembly.tex:21–51`,
immutable revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace Matrix

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]

/-- Discarding a possibly zero or subnormalized pure register retains its
actual squared norm as a scalar. Source: `eq:reference-junk`. -/
theorem partialTraceRight_tensorVector_eq_smul
    (Ω : EuclideanSpace ℂ a) (Ξ : EuclideanSpace ℂ b) :
    partialTraceRight (euclideanOuterProduct
      (euclideanTensorVector Ω Ξ) (euclideanTensorVector Ω Ξ)) =
        (‖Ξ‖ : ℂ) ^ 2 • euclideanOuterProduct Ω Ω := by
  rw [euclideanOuterProduct_tensorVector, partialTraceRight_kronecker,
    trace_euclideanOuterProduct_self]

/-- A subnormalized private factor contributes at most its lost squared norm
to the physical density error. Source: `eq:reference-junk` and
`eq:protocol-density`. -/
theorem rectangularTraceNorm_product_reference_sub_le
    (Ω : EuclideanSpace ℂ a) (Ξ : EuclideanSpace ℂ b)
    (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) :
    rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct
        (euclideanTensorVector Ω Ξ) (euclideanTensorVector Ω Ξ)) -
        euclideanOuterProduct Ω Ω) ≤ 1 - ‖Ξ‖ ^ 2 := by
  have hsq : ‖Ξ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Ξ]
  have hscalar : ‖(‖Ξ‖ : ℂ) ^ 2 - 1‖ = 1 - ‖Ξ‖ ^ 2 := by
    calc
      _ = ‖((‖Ξ‖ ^ 2 - 1 : ℝ) : ℂ)‖ := by
        rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one]
      _ = 1 - ‖Ξ‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
  have hdiff : (‖Ξ‖ : ℂ) ^ 2 • euclideanOuterProduct Ω Ω -
      euclideanOuterProduct Ω Ω =
        ((‖Ξ‖ : ℂ) ^ 2 - 1) • euclideanOuterProduct Ω Ω := by
    rw [sub_smul, one_smul]
  rw [partialTraceRight_tensorVector_eq_smul, hdiff,
    rectangularTraceNorm_smul, hscalar]
  have hρ : rectangularTraceNorm (euclideanOuterProduct Ω Ω) ≤ 1 := by
    simpa only [hΩ, one_mul] using rectangularTraceNorm_euclideanOuterProduct_le Ω Ω
  exact (mul_le_mul_of_nonneg_left hρ (by linarith)).trans_eq (mul_one _)

/-- Exact private-norm-loss form of the density estimate. The error is
absolute: there is no division by a success amplitude or dependence on the
private dimension. Source: §8.1, `eq:protocol-density`. -/
theorem rectangularTraceNorm_partialTraceRight_sub_product_reference_le
    (Ψ : EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) :
    rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct Ψ Ψ) - euclideanOuterProduct Ω Ω) ≤
        2 * ‖Ψ - euclideanTensorVector Ω Ξ‖ + (1 - ‖Ξ‖ ^ 2) := by
  have href : ‖euclideanTensorVector Ω Ξ‖ ≤ 1 := by
    simpa only [norm_euclideanTensorVector, hΩ, one_mul] using hΞ
  calc
    _ = rectangularTraceNorm
        ((partialTraceRight (euclideanOuterProduct Ψ Ψ) -
          partialTraceRight (euclideanOuterProduct
            (euclideanTensorVector Ω Ξ) (euclideanTensorVector Ω Ξ))) +
          (partialTraceRight (euclideanOuterProduct
            (euclideanTensorVector Ω Ξ) (euclideanTensorVector Ω Ξ)) -
            euclideanOuterProduct Ω Ω)) := by rw [sub_add_sub_cancel]
    _ ≤ _ := (rectangularTraceNorm_add_le _ _).trans
      (add_le_add
        (rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two
          Ψ (euclideanTensorVector Ω Ξ) hΨ href)
        (rectangularTraceNorm_product_reference_sub_le Ω Ξ hΩ hΞ))

/-- If `Ψ` is within `ε` of a unit physical vector tensored with a private
vector of norm in `[1 - δ, 1]`, its physical density error is at most
`2ε + 2δ`. The hypotheses imply nonnegative error budgets; no condition
`δ ≤ 1` is needed. Source: §8.1, `eq:protocol-density`. -/
theorem rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le
    (Ψ : EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1)
    (hΞ : ‖Ξ‖ ≤ 1) {ε δ : ℝ}
    (herror : ‖Ψ - euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖) :
    rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct Ψ Ψ) - euclideanOuterProduct Ω Ω) ≤
        2 * ε + 2 * δ := by
  refine (rectangularTraceNorm_partialTraceRight_sub_product_reference_le
    Ψ Ω Ξ hΨ hΩ hΞ).trans ?_
  nlinarith [sq_nonneg (‖Ξ‖ - 1)]

/-- An arbitrary compressed operator adds only its own absolute error to the
product-reference density estimate. Positivity and Hermiticity of `σ` are
not assumed. Source: `eq:protocol-density` and `eq:compressed-density`. -/
theorem rectangularTraceNorm_sub_pure_le_of_product_reference
    (σ : Matrix a a ℂ) (Ψ : EuclideanSpace ℂ (a × b))
    (Ω : EuclideanSpace ℂ a) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) {ε δ κ : ℝ}
    (herror : ‖Ψ - euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖)
    (hcompression : rectangularTraceNorm
      (σ - partialTraceRight (euclideanOuterProduct Ψ Ψ)) ≤ κ) :
    rectangularTraceNorm (σ - euclideanOuterProduct Ω Ω) ≤ κ + 2 * ε + 2 * δ := by
  calc
    _ = rectangularTraceNorm
        ((σ - partialTraceRight (euclideanOuterProduct Ψ Ψ)) +
          (partialTraceRight (euclideanOuterProduct Ψ Ψ) -
            euclideanOuterProduct Ω Ω)) := by rw [sub_add_sub_cancel]
    _ ≤ κ + (2 * ε + 2 * δ) := (rectangularTraceNorm_add_le _ _).trans
      (add_le_add hcompression
        (rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le
          Ψ Ω Ξ hΨ hΩ hΞ herror hlower))
    _ = _ := by ring

/-- The same joint vector retains norm at least `1 - δ - ε`; this does not
require the vector itself to be contractive. Source: §8.1, the normalization
estimate preceding `eq:protocol-density`. -/
theorem one_sub_le_norm_of_product_reference
    (Ψ : EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΩ : ‖Ω‖ = 1) {ε δ : ℝ}
    (herror : ‖Ψ - euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖) :
    1 - δ - ε ≤ ‖Ψ‖ := by
  have hreverse := norm_sub_norm_le (euclideanTensorVector Ω Ξ) Ψ
  rw [norm_euclideanTensorVector, hΩ, one_mul, norm_sub_rev] at hreverse
  linarith

/-- The unnormalized physical density has trace deficit at most `2(δ + ε)`.
This remains valid when the lower bound `1 - δ - ε` is negative, so no
small-error premise is hidden in the estimate. Source: §8.1, normalization
information retained until the last private trace. -/
theorem trace_deficit_partialTraceRight_le_of_product_reference
    (Ψ : EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΩ : ‖Ω‖ = 1) {ε δ : ℝ}
    (herror : ‖Ψ - euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖) :
    1 - (partialTraceRight (euclideanOuterProduct Ψ Ψ)).trace.re ≤ 2 * (δ + ε) := by
  rw [trace_partialTraceRight, trace_euclideanOuterProduct_self,
    ← Complex.ofReal_pow, Complex.ofReal_re]
  have hnorm := one_sub_le_norm_of_product_reference Ψ Ω Ξ hΩ herror hlower
  nlinarith [sq_nonneg (‖Ψ‖ - 1)]

end Matrix
