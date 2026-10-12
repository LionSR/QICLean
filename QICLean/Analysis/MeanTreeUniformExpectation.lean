/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Analysis.OperatorMean.MatrixPowers

/-!
# Uniform leaf bounds and inverse powers of a matrix mean tree

A common bound on the quadratic forms at the leaves bounds the quadratic
form at the root. For a unit vector, spectral Jensen gives the corresponding
bound for every root power between zero and one. Cauchy–Schwarz with opposite
powers then bounds an overlap by the squared norm after an inverse power.

These are the two Jensen steps and the final Cauchy–Schwarz step in the rough
upper comparison. The geometric hypotheses needed to obtain the common leaf
bound, and the Bell-coordinate identities, are separate results.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, `06-transport.tex`, `transport:vector-jensen`, and
`07-comparators.tex`, lines 367–381, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

/-- Cauchy–Schwarz applied to opposite real powers of a positive definite
matrix. No normalization or restriction on the real exponent is needed.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 374–381. -/
private theorem PosDef.norm_inner_sq_le_rpow_expectation_mul_norm_sq
    (hM : M.PosDef) (s : ℝ) (φ u : EuclideanSpace ℂ n) :
    ‖inner ℂ φ u‖ ^ 2 ≤
      (inner ℂ φ (toEuclideanLin (M ^ (2 * s)) φ)).re *
        ‖toEuclideanLin (M ^ (-s)) u‖ ^ 2 := by
  have hsym : (toEuclideanLin (M ^ s)).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (hM.rpow_isHermitian s)
  have hcancel : inner ℂ (toEuclideanLin (M ^ s) φ)
      (toEuclideanLin (M ^ (-s)) u) = inner ℂ φ u := by
    rw [hsym φ (toEuclideanLin (M ^ (-s)) u)]
    change inner ℂ φ ((toLpLin 2 2 (M ^ s) ∘ₗ toLpLin 2 2 (M ^ (-s))) u) = _
    rw [← toLpLin_mul_same, hM.rpow_mul_rpow_neg, toLpLin_one, LinearMap.id_apply]
  have hnorm : ‖toEuclideanLin (M ^ s) φ‖ ^ 2 =
      (inner ℂ φ (toEuclideanLin (M ^ (2 * s)) φ)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hsym φ (toEuclideanLin (M ^ s) φ)]
    change (inner ℂ φ ((toLpLin 2 2 (M ^ s) ∘ₗ toLpLin 2 2 (M ^ s)) φ)).re = _
    rw [← toLpLin_mul_same, hM.rpow_mul_rpow, ← two_mul]
  calc
    ‖inner ℂ φ u‖ ^ 2 =
        ‖inner ℂ (toEuclideanLin (M ^ s) φ) (toEuclideanLin (M ^ (-s)) u)‖ ^ 2 := by
      rw [hcancel]
    _ ≤ (‖toEuclideanLin (M ^ s) φ‖ * ‖toEuclideanLin (M ^ (-s)) u‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = (inner ℂ φ (toEuclideanLin (M ^ (2 * s)) φ)).re *
        ‖toEuclideanLin (M ^ (-s)) u‖ ^ 2 := by rw [mul_pow, hnorm]

end Matrix

namespace Matrix.MeanTree

variable {ι n : Type*} [Finite ι] [Fintype n] [DecidableEq n]
  {A : ι → Matrix n n ℂ}

private theorem re_inner_toEuclideanLin (M : Matrix n n ℂ)
    (φ : EuclideanSpace ℂ n) :
    (inner ℂ φ (Matrix.toEuclideanLin M φ)).re =
      (star (WithLp.ofLp φ) ⬝ᵥ (M *ᵥ WithLp.ofLp φ)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
  exact congrArg Complex.re (dotProduct_comm _ _)

/-- A common positive bound on the leaf quadratic forms also bounds the root
quadratic form. The vector need not be normalized.

Source: OpenAI area-law manuscript, `06-transport.tex`,
`transport:vector-jensen`, and `07-comparators.tex`, lines 367–375. -/
theorem re_inner_eval_le_of_forall (hA : ∀ j, (A j).PosDef)
    (T : MeanTree ι) (φ : EuclideanSpace ℂ n) {L : ℝ} (hL : 0 < L)
    (hleaf : ∀ j, (inner ℂ φ (Matrix.toEuclideanLin (A j) φ)).re ≤ L) :
    (inner ℂ φ (Matrix.toEuclideanLin (T.eval A) φ)).re ≤ L := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [re_inner_toEuclideanLin]
  refine (T.re_dotProduct_eval_le hA (WithLp.ofLp φ)).trans ?_
  calc
    (∏ j, (star (WithLp.ofLp φ) ⬝ᵥ (A j *ᵥ WithLp.ofLp φ)).re ^ T.weight j)
        ≤ ∏ j, L ^ T.weight j := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Real.rpow_nonneg ((hA j).posSemidef.re_dotProduct_nonneg _) _
      · intro j _
        apply Real.rpow_le_rpow ((hA j).posSemidef.re_dotProduct_nonneg _)
        · simpa only [re_inner_toEuclideanLin, RCLike.re_eq_complex_re] using hleaf j
        · exact T.weight_nonneg j
    _ = L := by rw [← Real.rpow_sum_of_pos hL, T.sum_weight, Real.rpow_one]

/-- For a unit vector, a common leaf bound also bounds every root power in
`[0,1]`. This is spectral Jensen following the tree Jensen inequality.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 374–378. -/
theorem re_inner_rpow_eval_le_of_forall (hA : ∀ j, (A j).PosDef)
    (T : MeanTree ι) (φ : EuclideanSpace ℂ n) (hφ : ‖φ‖ = 1)
    {L p : ℝ} (hL : 0 < L) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hleaf : ∀ j, (inner ℂ φ (Matrix.toEuclideanLin (A j) φ)).re ≤ L) :
    (inner ℂ φ (Matrix.toEuclideanLin ((T.eval A) ^ p) φ)).re ≤ L ^ p := by
  have hM := T.posDef_eval hA
  have hunit : (star (WithLp.ofLp φ) ⬝ᵥ WithLp.ofLp φ).re = 1 := by
    have h := norm_sq_eq_re_inner (𝕜 := ℂ) φ
    rw [hφ, one_pow, EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa only [RCLike.re_eq_complex_re, dotProduct_comm] using h.symm
  rw [re_inner_toEuclideanLin]
  have hj := Matrix.re_dotProduct_rpow_mulVec_le hM.posSemidef hp (WithLp.ofLp φ)
  rw [hunit, Real.one_rpow, one_mul] at hj
  refine hj.trans (Real.rpow_le_rpow (hM.posSemidef.re_dotProduct_nonneg _) ?_ hp.1)
  simpa only [re_inner_toEuclideanLin] using
    T.re_inner_eval_le_of_forall hA φ hL hleaf

/-- A common leaf bound controls the overlap with any vector by the norm of
that vector after the opposite root power. No normalization of `u` is required.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 374–381. -/
theorem norm_inner_sq_le_rpow_mul_inverse_norm_sq (hA : ∀ j, (A j).PosDef)
    (T : MeanTree ι) (φ u : EuclideanSpace ℂ n) (hφ : ‖φ‖ = 1)
    {L s : ℝ} (hL : 0 < L) (hs : 2 * s ∈ Set.Icc (0 : ℝ) 1)
    (hleaf : ∀ j, (inner ℂ φ (Matrix.toEuclideanLin (A j) φ)).re ≤ L) :
    ‖inner ℂ φ u‖ ^ 2 ≤
      L ^ (2 * s) * ‖Matrix.toEuclideanLin ((T.eval A) ^ (-s)) u‖ ^ 2 := by
  refine ((T.posDef_eval hA).norm_inner_sq_le_rpow_expectation_mul_norm_sq s φ u).trans ?_
  exact mul_le_mul_of_nonneg_right
    (T.re_inner_rpow_eval_le_of_forall hA φ hφ hL hs hleaf) (sq_nonneg _)

end Matrix.MeanTree
