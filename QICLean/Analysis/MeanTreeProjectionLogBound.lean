/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeProjectionSectors
import QICLean.Analysis.ProjectionCalculus
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
