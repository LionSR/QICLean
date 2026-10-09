/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MeanTreeIntertwine

/-!
# Weighted means on two complementary projection ranges

Let `P` be an orthogonal projection. Suppose that each leaf of a weighted
mean tree is scalar on the range of `P` and on its orthogonal complement,
with the same positive scalar `b` on the complement. The root has scalar
`b` on the complement and the weighted geometric mean of the leaf scalars
on the range of `P`.

This identity and monotonicity pass a two-sector lower comparison through
the tree. The original leaf operators need not commute with `P` or with
each other. Repeated leaf labels and zero edge weights are permitted.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 603–621, in the proof of
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem projection_sectors_mul {P : Matrix n n ℂ}
    (hP : IsStarProjection P) (a b c d : ℝ) :
    (a • (1 - P) + b • P) * (c • (1 - P) + d • P) =
      (a * c) • (1 - P) + (b * d) • P := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hP.one_sub.isIdempotentElem.eq, hP.isIdempotentElem.eq,
    hP.mul_one_sub_self, hP.one_sub_mul_self, smul_zero, add_zero, zero_add]
  rw [mul_comm c a, mul_comm d b]

/-- Positive scalar values on two complementary orthogonal ranges define a
positive definite operator. Used for the two-sector comparison in
`07-comparators.tex`, lines 603–621. -/
theorem posDef_smul_one_sub_add_smul_projection {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (b • (1 - P) + d • P).PosDef := by
  have hnonneg : 0 ≤ b • (1 - P) + d • P :=
    add_nonneg (smul_nonneg hb.le hP.one_sub.nonneg) (smul_nonneg hd.le hP.nonneg)
  refine (nonneg_iff_posSemidef.mp hnonneg).posDef_iff_isUnit.mpr ?_
  refine isUnit_iff_exists_inv.mpr ⟨b⁻¹ • (1 - P) + d⁻¹ • P, ?_⟩
  rw [projection_sectors_mul hP, mul_inv_cancel₀ hb.ne', mul_inv_cancel₀ hd.ne',
    one_smul, one_smul, sub_add_cancel]

namespace MeanTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A mean tree acts independently on the two complementary ranges of an
orthogonal projection. The common scalar on the complement is unchanged.
Source: `07-comparators.tex`, lines 603–621, `comparator:tree-log-lower`. -/
theorem eval_smul_one_sub_add_smul_projection {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hd : ∀ j, 0 < d j) (T : MeanTree ι) :
    T.eval (fun j ↦ b • (1 - P) + d j • P) =
      b • (1 - P) + (∏ j, (d j) ^ T.weight j) • P := by
  let A (j : ι) : Matrix n n ℂ := b • (1 - P) + d j • P
  have hA (j : ι) : (A j).PosDef :=
    posDef_smul_one_sub_add_smul_projection hP hb (hd j)
  have hsector (j : ι) : A j * P = P * (d j • (1 : Matrix n n ℂ)) := by
    simp only [A, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      hP.one_sub_mul_self, hP.isIdempotentElem.eq, smul_zero, zero_add]
  have hcomplement (j : ι) :
      A j * (1 - P) = (1 - P) * (b • (1 : Matrix n n ℂ)) := by
    simp only [A, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      hP.mul_one_sub_self, hP.one_sub.isIdempotentElem.eq, smul_zero, add_zero]
  have hsectorRoot := eval_intertwine hA
    (fun j ↦ (PosDef.one : (1 : Matrix n n ℂ).PosDef).smul (hd j)) P hsector T
  rw [eval_smul (fun _ ↦ (PosDef.one : (1 : Matrix n n ℂ).PosDef)) hd,
    eval_const PosDef.one, Matrix.mul_smul, Matrix.mul_one] at hsectorRoot
  have hcomplementRoot := eval_intertwine hA
    (fun _ ↦ (PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hb)
    (1 - P) hcomplement T
  rw [eval_const ((PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hb),
    Matrix.mul_smul, Matrix.mul_one] at hcomplementRoot
  change T.eval A = _
  calc
    T.eval A = T.eval A * ((1 - P) + P) := by rw [sub_add_cancel, Matrix.mul_one]
    _ = b • (1 - P) + (∏ j, (d j) ^ T.weight j) • P := by
      rw [Matrix.mul_add, hcomplementRoot, hsectorRoot]

/-- Two-sector lower bounds pass through a mean tree. The original operators
are not required to commute with the projection or with one another.
Source: `07-comparators.tex`, lines 603–621, `comparator:tree-log-lower`. -/
theorem smul_one_sub_add_smul_projection_le_eval {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hd : ∀ j, 0 < d j) {A : ι → Matrix n n ℂ}
    (hbound : ∀ j, b • (1 - P) + d j • P ≤ A j) (T : MeanTree ι) :
    b • (1 - P) + (∏ j, (d j) ^ T.weight j) • P ≤ T.eval A := by
  rw [← eval_smul_one_sub_add_smul_projection hP hb hd T]
  exact eval_mono (fun j ↦ posDef_smul_one_sub_add_smul_projection hP hb (hd j)) hbound T

end MeanTree

end Matrix
