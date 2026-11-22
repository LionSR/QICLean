/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MeanTreeProjectionSectors
import QICLean.Analysis.FunctionalCalculus.OrthogonalResolutionCfc
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Logarithmic lower bounds from two projection ranges

A positive two-sector comparison can be passed through a weighted mean tree
and then through the operator logarithm. The complementary scalar remains
fixed, while the scalar on the distinguished range becomes the terminally
weighted average of its logarithms.

No commutation of the original leaf operators with the distinguished
projection is required. Strict positivity follows from the positive
comparison operators. All terminal weights, including zero weights, are
retained.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 603–640,
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The logarithm of a mean tree dominates the logarithm of its two-sector
comparison. The original leaves need not commute with the projection or
with one another. Source: `07-comparators.tex`, lines 603–640,
`comparator:tree-log-lower`. -/
theorem log_projection_sectors_le_log_eval {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hd : ∀ j, 0 < d j) {A : ι → Matrix n n ℂ}
    (hbound : ∀ j, b • (1 - P) + d j • P ≤ A j) (T : MeanTree ι) :
    Real.log b • (1 - P) + (∑ j, T.weight j * Real.log (d j)) • P ≤
      CFC.log (T.eval A) := by
  let r : ℝ := ∏ j, (d j) ^ T.weight j
  have hr : 0 < r := Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hd j) _
  have hlogr : Real.log r = ∑ j, T.weight j * Real.log (d j) := by
    dsimp only [r]
    rw [Real.log_prod (fun j _ ↦ (Real.rpow_pos_of_pos (hd j) _).ne')]
    exact Finset.sum_congr rfl fun j _ ↦ Real.log_rpow (hd j) _
  have hpositive : (b • (1 - P) + r • P).PosDef :=
    Matrix.posDef_smul_one_sub_add_smul_projection hP hb hr
  have horder : b • (1 - P) + r • P ≤ T.eval A :=
    smul_one_sub_add_smul_projection_le_eval hP hb hd hbound T
  have hlog := CFC.log_le_log horder hpositive.isStrictlyPositive
  have haffine : b • (1 - P) + r • P =
      b • (1 : Matrix n n ℂ) + (r - b) • P := by
    rw [smul_sub, sub_smul]
    abel
  rw [CFC.log, haffine,
    Matrix.cfc_affine_of_isSelfAdjoint_isIdempotentElem P hP.isSelfAdjoint
      hP.isIdempotentElem b r Real.log, hlogr] at hlog
  exact hlog

end Matrix.MeanTree

section MeanTreeProjectionMassBound

/-!
# A logarithmic lower bound from retained projection mass

Suppose that the leaves dominate positive matrices which are scalar on
two complementary projection ranges. If a unit vector has mass at least
`1 - δ` on the distinguished range, its logarithmic expectation at the
root is bounded below by the weighted logarithmic value on that range,
less `δ` times the difference of the two logarithmic values.

The distinguished scalar is assumed to be at least the complementary
scalar. In the lower area-law comparison this follows from averaging
the positive whole-space bound with the positive projection bound.
No upper bound on `δ` is required.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 603–640,
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Retained projection mass gives the lower logarithmic expectation of a
weighted mean tree. The error is linear in the mass deficit, uniformly
over the terminal probabilities, including zero probabilities.
Source: `07-comparators.tex`, lines 603–640,
`comparator:tree-log-lower`. -/
theorem re_dotProduct_log_eval_ge_of_projection_mass {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hbd : ∀ j, b ≤ d j) {A : ι → Matrix n n ℂ}
    (hbound : ∀ j, b • (1 - P) + d j • P ≤ A j) (T : MeanTree ι)
    (v : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) {δ : ℝ}
    (hmass : 1 - δ ≤ (star v ⬝ᵥ (P *ᵥ v)).re) :
    let ell := ∑ j, T.weight j * Real.log (d j)
    ell - δ * (ell - Real.log b) ≤
      (star v ⬝ᵥ (CFC.log (T.eval A) *ᵥ v)).re := by
  intro ell
  have hell : Real.log b ≤ ell := by
    calc
      Real.log b = ∑ j, T.weight j * Real.log b := by
        rw [← Finset.sum_mul, T.sum_weight, one_mul]
      _ ≤ ell := Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (Real.log_le_log hb (hbd j)) (T.weight_nonneg j)
  have horder := log_projection_sectors_le_log_eval hP hb
    (fun j ↦ hb.trans_le (hbd j)) hbound T
  have hreal := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp horder).dotProduct_mulVec_nonneg v)).1
  simp only [sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, one_mulVec, Complex.sub_re, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hreal
  have hn : (star v ⬝ᵥ v).re = 1 := by
    have hnorm : (star v ⬝ᵥ v).re = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm]
      rfl
    simpa only [hv, one_pow] using hnorm
  rw [hn] at hreal
  have hmass' := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hell)
  change 0 ≤ (star v ⬝ᵥ (CFC.log (T.eval A) *ᵥ v)).re -
    (Real.log b * (1 - (star v ⬝ᵥ (P *ᵥ v)).re) +
      ell * (star v ⬝ᵥ (P *ᵥ v)).re) at hreal
  nlinarith only [hreal, hmass']

end Matrix.MeanTree
end

end MeanTreeProjectionMassBound
