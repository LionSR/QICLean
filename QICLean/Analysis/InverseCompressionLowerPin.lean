/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Bounds from a compressed inverse

A bound for the compression of the inverse of a positive-definite matrix yields
a lower bound for the matrix itself. The projection need not commute with the matrix.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `07-comparators.tex`, `comparator:inverse-compression` and `comparator:lower-pin`,
  lines 585–605, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The two Gram matrices have the same operator-norm bound. -/
theorem mul_conjTranspose_le_smul_one_of_conjTranspose_mul_le
    (T : Matrix n n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : Tᴴ * T ≤ c • (1 : Matrix n n ℂ)) :
    T * Tᴴ ≤ c • (1 : Matrix n n ℂ) := by
  have hn : ‖Tᴴ * T‖ ≤ c :=
    (CStarAlgebra.norm_le_iff_le_algebraMap (Tᴴ * T) hc
      (star_mul_self_nonneg T)).mpr (by simpa only [Algebra.algebraMap_eq_smul_one] using h)
  change ‖star T * T‖ ≤ c at hn
  have hsq : ‖T‖ ^ 2 ≤ c := by
    simpa only [CStarRing.norm_star_mul_self, pow_two] using hn
  exact (CStarAlgebra.mul_star_le_algebraMap_norm_sq T).trans
    (by simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right hsq (zero_le_one : (0 : Matrix n n ℂ) ≤ 1))

/-- A compressed-inverse bound implies a lower bound on the original matrix.
No commutation between the matrix and the projection is assumed.
Source: two-dimensional area law, `07-comparators.tex`,
`comparator:inverse-compression` and `comparator:lower-pin`, lines 585–605. -/
theorem PosDef.inv_smul_projection_le_of_compression_inv_le
    {A P : Matrix n n ℂ} (hA : A.PosDef) (hP : IsStarProjection P)
    {c : ℝ} (hc : 0 < c) (h : P * A⁻¹ * P ≤ c • P) :
    c⁻¹ • P ≤ A := by
  have hPone : P ≤ 1 := sub_nonneg.mp hP.one_sub.nonneg
  have hbound : P * A⁻¹ * P ≤ c • (1 : Matrix n n ℂ) :=
    h.trans (smul_le_smul_of_nonneg_left hPone hc.le)
  let S := CFC.sqrt A
  have hSpositive : IsStrictlyPositive S := IsStrictlyPositive.sqrt A hA.isStrictlyPositive
  have hS : S.PosDef := Matrix.IsStrictlyPositive.posDef hSpositive
  have hSq : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit)
  have hSi : S⁻¹ᴴ = S⁻¹ := hS.inv.isHermitian.eq
  have hPi : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hSiSq : S⁻¹ * S⁻¹ = A⁻¹ := by rw [← Matrix.mul_inv_rev, hSq]
  let T := S⁻¹ * P
  have hgram : Tᴴ * T = P * A⁻¹ * P := by
    simp only [T, Matrix.conjTranspose_mul, hPi, hSi]
    calc
      P * S⁻¹ * (S⁻¹ * P) = P * (S⁻¹ * S⁻¹) * P := by simp only [Matrix.mul_assoc]
      _ = P * A⁻¹ * P := by rw [hSiSq]
  have hTT : T * Tᴴ ≤ c • (1 : Matrix n n ℂ) :=
    mul_conjTranspose_le_smul_one_of_conjTranspose_mul_le T hc.le
      (hgram.symm ▸ hbound)
  have hST : S * T = P := by
    change S * (S⁻¹ * P) = P
    rw [← Matrix.mul_assoc, hSSi, Matrix.one_mul]
  have hTS : Tᴴ * S = P := by
    simpa only [Matrix.conjTranspose_mul, hS.isHermitian.eq, hPi] using
      congrArg Matrix.conjTranspose hST
  have hconj := hS.posSemidef.isHermitian.isSelfAdjoint.conjugate_le_conjugate hTT
  have hPA : P ≤ c • A := by
    convert hconj using 1
    · symm
      calc
        S * (T * Tᴴ) * S = (S * T) * (Tᴴ * S) := by simp only [Matrix.mul_assoc]
        _ = P := by rw [hST, hTS, hP.isIdempotentElem]
    · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSq]
  have hi := smul_le_smul_of_nonneg_left hPA (inv_nonneg.mpr hc.le)
  simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hi

end Matrix
