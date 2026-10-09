/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectionCompressionCfc
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Functional bounds on an invariant projection range

A lower bound for a Hermitian matrix on a commuting orthogonal projection
range controls any scalar function bounded above on the corresponding
half-line. In particular, a lower bound on that range yields an upper
bound for a negative exponential on the same range.

The argument uses the matrix order on the range, not a bound for a single
vector's expectation. Extend the restricted matrix by the lower-bound
scalar on the complementary range, apply scalar functional calculus, and
compress back to the original range.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 481–493,
  `comparator:good-auxiliary`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An upper scalar bound above the compressed spectral floor gives an
operator bound on an invariant projection range. No continuity assumption
on the scalar function is needed in finite dimension.
Source: the auxiliary support estimate in `07-comparators.tex`, lines 481–493. -/
theorem IsHermitian.compression_cfc_le_of_lower_bound
    {A P : Matrix n n ℂ} (hA : A.IsHermitian) (hP : IsStarProjection P)
    (hAP : Commute A P) {b c : ℝ} (hbound : b • P ≤ P * A * P)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, b ≤ x → f x ≤ c) :
    P * cfc f A * P ≤ c • P := by
  classical
  have hPH : P.IsHermitian := hP.isSelfAdjoint.isHermitian
  have hPP : P * P = P := hP.isIdempotentElem
  have hPAP : P * A * P = P * A := by
    rw [Matrix.mul_assoc, hAP.eq, ← Matrix.mul_assoc, hPP]
  let B := P * A + b • (1 - P)
  have hB : B.IsHermitian := by
    simp only [B, IsHermitian, conjTranspose_add, conjTranspose_mul,
      conjTranspose_smul, conjTranspose_sub, conjTranspose_one,
      hA.eq, hPH.eq, star_trivial, hAP.eq]
  have hfloor : b • (1 : Matrix n n ℂ) ≤ B := by
    calc
      b • (1 : Matrix n n ℂ) = b • P + b • (1 - P) := by
        rw [← smul_add, add_sub_cancel]
      _ ≤ P * A + b • (1 - P) :=
        add_le_add_left (by simpa only [hPAP] using hbound) _
  have hspectrum : ∀ x ∈ spectrum ℝ B, b ≤ x :=
    (algebraMap_le_iff_le_spectrum hB.isSelfAdjoint).mp
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor)
  have hcfc : cfc f B ≤ c • (1 : Matrix n n ℂ) := by
    have h := (cfc_le_algebraMap_iff f c B
      (hf := Matrix.finite_real_spectrum.continuousOn f) (ha := hB.isSelfAdjoint)).mpr
        (fun x hx ↦ hf x (hspectrum x hx))
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  have hPB : P * B = P * A := by
    simp only [B, Matrix.mul_add, ← Matrix.mul_assoc, hPP,
      Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, sub_self,
      smul_zero, add_zero]
  have hsame : P * cfc f B = P * cfc f A :=
    mul_cfc_eq_mul_cfc_of_mul_eq hB hA hAP.symm hPB f
  have hcompressed : P * cfc f B * P ≤ c • P := by
    rw [Matrix.le_iff]
    simpa only [hPH.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hPP] using
      (Matrix.le_iff.mp hcfc).conjTranspose_mul_mul_same P
  rw [hsame] at hcompressed
  exact hcompressed

/-- A compressed lower bound controls the negative exponential on the same
invariant range. This conclusion uses an operator lower bound, rather than
an expectation bound. Source: `07-comparators.tex`, lines 481–493,
`comparator:good-auxiliary`. -/
theorem IsHermitian.compression_exp_neg_smul_le_of_lower_bound
    {A P : Matrix n n ℂ} (hA : A.IsHermitian) (hP : IsStarProjection P)
    (hAP : Commute A P) {b : ℝ} (hbound : b • P ≤ P * A * P)
    {a : ℝ} (ha : 0 ≤ a) :
    P * NormedSpace.exp ((-a) • A) * P ≤ Real.exp (-a * b) • P := by
  have h := hA.compression_cfc_le_of_lower_bound hP hAP hbound
    (fun x ↦ Real.exp (-a * x)) (fun x hx ↦
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr ha)))
  rw [cfc_comp_const_mul (-a) Real.exp A,
    CFC.real_exp_eq_normedSpace_exp
      (hA.smul (show IsSelfAdjoint (-a) by simp [isSelfAdjoint_iff])).isSelfAdjoint] at h
  exact h

end Matrix
