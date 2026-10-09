/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Exponential order for commuting Hermitian matrices

The exponential preserves order between commuting Hermitian matrices. The proof
writes their positive difference as `D` and uses `exp(D) ≥ 1`, together with
`exp(B)-exp(A)=exp(A)(exp(D)-1)`. Positivity of this last product follows from
commutation.

This is the scalar functional-calculus comparison used for the whole and grouped
copy labels in OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 455--476,
`comparator:restriction-dimensions` and `comparator:whole-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponentiating an order comparison is valid for commuting Hermitian matrices.
Source: the common-label comparison in `07-comparators.tex`, lines 455--476. -/
theorem IsHermitian.exp_le_exp_of_commute {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (h : A ≤ B) :
    NormedSpace.exp A ≤ NormedSpace.exp B := by
  have hD : IsSelfAdjoint (B - A) := (hB.sub hA).isSelfAdjoint
  have hDnonneg : 0 ≤ B - A := sub_nonneg.mpr h
  have hOne : 1 ≤ NormedSpace.exp (B - A) := by
    rw [← CFC.real_exp_eq_normedSpace_exp hD]
    exact one_le_cfc Real.exp (B - A)
      (fun x hx => Real.one_le_exp (spectrum_nonneg_of_nonneg hDnonneg hx))
      (ha := hD)
  have hAD : Commute A (B - A) := hAB.sub_right (Commute.refl A)
  have hprod : 0 ≤ NormedSpace.exp A * (NormedSpace.exp (B - A) - 1) :=
    Commute.mul_nonneg hA.isSelfAdjoint.exp_nonneg (sub_nonneg.mpr hOne)
      (hAD.exp.sub_right (Commute.one_right _))
  rw [mul_sub, mul_one, ← NormedSpace.exp_add_of_commute hAD,
    show A + (B - A) = B by abel] at hprod
  exact sub_nonneg.mp hprod

end Matrix
