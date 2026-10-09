/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InverseCompressionLowerPin

/-!
# Lower projection bounds in fixed coordinates

A lower bound obtained from a compressed inverse may first be transported
along a coordinate equivalence and then compressed by a rectangular
matrix. The compressed inverse bound is used in its original coordinates;
positivity then transports the conclusion to the fixed coordinates.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 585--615, `comparator:lower-pin`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- A compressed-inverse bound gives the lower pin in any fixed rectangular
coordinates, after a literal coordinate equivalence. No commutation of
the original matrix with the projection is required. Source:
`07-comparators.tex`, `comparator:lower-pin`, lines 585--600. -/
theorem PosDef.lower_pin_of_reindexed_inverse_compression
    {m n l : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype l]
    {A : Matrix m m ℂ} (hA : A.PosDef) (e : m ≃ n)
    {P : Matrix n n ℂ} (hP : IsStarProjection P)
    {c : ℝ} (hc : 0 < c)
    (hinv : P * (A⁻¹).submatrix e.symm e.symm * P ≤ c • P)
    (Z : Matrix m l ℂ) :
    c⁻¹ • (Zᴴ * P.submatrix e e * Z) ≤ Zᴴ * A * Z := by
  have hnative : c⁻¹ • P ≤ A.submatrix e.symm e.symm :=
    (hA.submatrix e.symm.injective).inv_smul_projection_le_of_compression_inv_le
      hP hc (by simpa only [Matrix.inv_submatrix_equiv] using hinv)
  have hpull : c⁻¹ • P.submatrix e e ≤ A := by
    apply Matrix.le_iff.mpr
    simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul,
      Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply,
      Matrix.submatrix_id_id] using
      (Matrix.le_iff.mp hnative).submatrix e
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using
    (Matrix.le_iff.mp hpull).conjTranspose_mul_mul_same Z

end Matrix
