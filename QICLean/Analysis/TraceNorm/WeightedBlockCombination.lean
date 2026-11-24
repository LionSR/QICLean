/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.Composition
import QICLean.Analysis.Norm.WeightedRectangular

/-!
# Weighted combinations of the blocks of a rectangular contraction

The `(l, i)` blocks `(Matrix.comp L I U T ℂ).symm O l i` of a rectangular matrix `O` on
`(L × U) × (I × T)`, weighted by square roots of probability vectors on `T` and `U`, combine
into the matrix `Matrix.halfWeightedBlockCombination`, whose trace norm is bounded by the
Hilbert–Schmidt norm of a quarter-weighted combination. For a contraction `O`, the
variance-weighted sum of the blocks is at most one, with no dimension factor. Ordinary
transpose, not the adjoint, appears, so complex coefficients keep their phases.

## Main definitions

* `Matrix.halfWeightedBlockCombination`, `Matrix.quarterWeightedBlockCombination`: the two
  weighted combinations of the transposed blocks and of the blocks.
* `Matrix.productWeight`: the product `p i τ t` of two weights on a product type.

## Main results

* `Matrix.rectangularTraceNorm_halfWeightedBlockCombination_le`
* `Matrix.sum_sqrt_mul_frobeniusNormSq_quarterWeighted_block_le_one`

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
  `eq:compression-block-second-moment`, `eq:compression-dimension-free`, and
  `eq:compression-one-choice`, `04-compression.tex:383–538`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These are original proofs. No OpenAI Lean code is
  copied or adapted.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder ComplexConjugate

noncomputable section

namespace Matrix

variable {I L T U : Type*} [Fintype I] [Fintype L] [Fintype T] [Fintype U]
  [DecidableEq I] [DecidableEq L] [DecidableEq T] [DecidableEq U]

/-- The combination `∑_b z_b D_τ^{1/2} (O_{b.2, b.1})ᵀ D_τ'^{1/2}` of the transposed blocks of `O`,
with square-root weights on both sides. The transpose is the ordinary transpose, not the
adjoint. Source: `eq:compression-exterior-input`. -/
def halfWeightedBlockCombination (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) : Matrix T U ℂ :=
  ∑ b, z b • Matrix.halfWeighted tau tau' ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)ᵀ

/-- The combination `∑_b z_b D_τ'^{1/4} O_{b.2, b.1} D_τ^{1/4}` of the blocks of `O`, with
quarter-power weights on both sides.
Source: the transpose step after `eq:compression-quarter-powers`. -/
def quarterWeightedBlockCombination (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) : Matrix U T ℂ :=
  ∑ b, z b • Matrix.quarterWeighted tau' tau ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)

omit [DecidableEq I] [DecidableEq L] in
/-- The square-root weighted combination is the square-root weighting of the combination of
the transposed blocks; no complex coefficient is conjugated. -/
theorem halfWeightedBlockCombination_eq_halfWeighted
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) :
    halfWeightedBlockCombination tau tau' O z =
      Matrix.halfWeighted tau tau' (∑ b, z b • ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)ᵀ) := by
  ext t u
  simp only [halfWeightedBlockCombination, Matrix.halfWeighted, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

omit [DecidableEq I] [DecidableEq L] in
/-- The quarter-power weighting of the combination of the transposed blocks is the transpose
of the quarter-weighted block combination, with every coefficient kept. -/
theorem quarterWeighted_sum_eq_transpose_quarterWeightedBlockCombination
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) :
    Matrix.quarterWeighted tau tau' (∑ b, z b • ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)ᵀ) =
      (quarterWeightedBlockCombination tau tau' O z)ᵀ := by
  ext t u
  simp only [quarterWeightedBlockCombination, Matrix.quarterWeighted_apply, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

omit [DecidableEq I] [DecidableEq L] in
/-- The trace norm of the square-root weighted combination is at most the Hilbert--Schmidt
norm of the quarter-weighted combination, with no dimension factor.
Source: `eq:compression-quarter-powers`. -/
theorem rectangularTraceNorm_halfWeightedBlockCombination_le
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    Matrix.rectangularTraceNorm (halfWeightedBlockCombination tau tau' O z) ≤
      Real.sqrt (Matrix.frobeniusNormSq (quarterWeightedBlockCombination tau tau' O z)) := by
  rw [halfWeightedBlockCombination_eq_halfWeighted]
  have h := Matrix.rectangularTraceNorm_halfWeighted_le tau tau'
    (∑ b, z b • ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)ᵀ) htau htau' htausum htau'sum
  rw [quarterWeighted_sum_eq_transpose_quarterWeightedBlockCombination] at h
  simpa only [Matrix.frobeniusNormSq, Matrix.frobenius_norm_transpose] using h

/-- The product weight `(i, t) ↦ p i τ t` on a product type. Source: the definition of `R`
and `Rtilde` after `eq:compression-block-second-moment`. -/
def productWeight (p : I → ℝ) (tau : T → ℝ) : I × T → ℝ :=
  fun b ↦ p b.1 * tau b.2

omit [DecidableEq I] [DecidableEq T] in
/-- The product of two probability vectors is a probability vector, including when some
weights vanish. -/
theorem sum_productWeight
    (p : I → ℝ) (tau : T → ℝ) (hp : ∑ i, p i = 1) (htau : ∑ t, tau t = 1) :
    ∑ b, productWeight p tau b = 1 := by
  simp only [productWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    htau, mul_one, hp]

/-- The blocks of `O`, weighted by `√(p_i p'_l)`, aggregate into the Hilbert--Schmidt square of
`O` weighted by the two product weights. Source: the equality preceding
`eq:compression-dimension-free`. -/
theorem sum_sqrt_mul_frobeniusNormSq_quarterWeighted_block
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l)
    :
    ∑ b : I × L, Real.sqrt (p b.1 * p' b.2) *
        Matrix.frobeniusNormSq
          (Matrix.quarterWeighted tau' tau ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)) =
      Matrix.frobeniusNormSq (Matrix.quarterWeighted
        (productWeight p' tau') (productWeight p tau) O) := by
  simp only [Matrix.frobeniusNormSq_quarterWeighted, productWeight,
    Matrix.comp_symm_apply, Fintype.sum_prod_type, Real.sqrt_mul (hp _),
    Real.sqrt_mul (hp' _)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i l ↦ _)]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm (f := fun i u ↦ _)]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  ring

omit [DecidableEq L] in
/-- For a contraction `O` and probability weights, the weighted sum of the Hilbert--Schmidt
squares of the quarter-weighted blocks is at most one, with no dimension factor.
Source: `eq:compression-dimension-free`. -/
theorem sum_sqrt_mul_frobeniusNormSq_quarterWeighted_block_le_one
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (hpsum : ∑ i, p i = 1) (hp'sum : ∑ l, p' l = 1)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) (hO : ‖O‖ ≤ 1) :
    ∑ b : I × L, Real.sqrt (p b.1 * p' b.2) *
      Matrix.frobeniusNormSq
        (Matrix.quarterWeighted tau' tau ((Matrix.comp _ _ _ _ ℂ).symm O b.2 b.1)) ≤ 1 := by
  classical
  rw [sum_sqrt_mul_frobeniusNormSq_quarterWeighted_block p p' tau tau' O hp hp']
  exact Matrix.frobeniusNormSq_quarterWeighted_le_one _ _ O
    (fun b ↦ mul_nonneg (hp' b.1) (htau' b.2))
    (fun b ↦ mul_nonneg (hp b.1) (htau b.2))
    (sum_productWeight p' tau' hp'sum htau'sum)
    (sum_productWeight p tau hpsum htausum) hO

end Matrix
