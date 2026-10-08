/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixAux
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# A weighted trace bound for commuting exponentials

For commuting Hermitian matrices, the exponential of their sum is the
product of their exponentials. Positivity of the weighted trace of the
square of their difference bounds this product by the arithmetic mean
of the two squares. The positive semidefinite weight need not have trace
one or commute with either matrix, and the exponent is any real number.

This is an auxiliary estimate for the rough merge-moment argument in
*A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 553–555. The manuscript uses a
Cauchy–Schwarz geometric-mean bound there; the arithmetic-mean bound
proved here also suffices when the two doubled moments are polynomially
bounded. Identifying the common-space merge deficits and proving their
commutation remain separate steps.
-/

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Positivity of the weighted trace of a Hermitian difference square gives
the arithmetic-mean product bound. OpenAI area-law manuscript,
`07-comparators.tex`, lines 553–555, auxiliary rough estimate. -/
private theorem re_trace_product_le_half_sum_squares {ρ A B : Matrix X X ℂ} (hρ : ρ.PosSemidef)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    2 * (ρ * (A * B)).trace.re ≤
      (ρ * (A * A)).trace.re + (ρ * (B * B)).trace.re := by
  have h := (Complex.nonneg_iff.mp
    (hρ.trace_mul_nonneg (posSemidef_conjTranspose_mul_self (A - B)))).1
  rw [(hA.sub hB).eq] at h
  simp only [sub_mul, mul_sub,
    trace_sub, Complex.sub_re, hAB.eq] at h
  rw [hAB.eq]
  linarith

/-
Provenance-ID: 8750-qic-weighted-trace-exponential-01
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.PosSemidef.re_trace_mul_exp_add_le_half_sum
Manuscript: September 24, 2026, comparator rough estimate, lines 553–555.
-/

open scoped Matrix.Norms.Operator in
/-- The weighted trace of the exponential of a sum of commuting Hermitian
matrices is at most the arithmetic mean of their doubled exponential
traces. The weight is positive semidefinite, without normalization or a
commutation requirement, and the exponent is any real number.
*A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 553–555. This is a separate auxiliary
arithmetic-mean estimate for the rough argument. -/
theorem PosSemidef.re_trace_mul_exp_add_le_half_sum {ρ A B : Matrix X X ℂ} (hρ : ρ.PosSemidef)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (a : ℝ) :
    (ρ * NormedSpace.exp ((a : ℂ) • (A + B))).trace.re ≤
      ((ρ * NormedSpace.exp (((2 * a : ℝ) : ℂ) • A)).trace.re +
        (ρ * NormedSpace.exp (((2 * a : ℝ) : ℂ) • B)).trace.re) / 2 := by
  have hA' : ((a : ℂ) • A).IsHermitian := hA.smul (by simp [isSelfAdjoint_iff])
  have hB' : ((a : ℂ) • B).IsHermitian := hB.smul (by simp [isSelfAdjoint_iff])
  have hAB' := (hAB.smul_left (a : ℂ)).smul_right (a : ℂ)
  have h := re_trace_product_le_half_sum_squares hρ
    hA'.isSelfAdjoint.exp.isHermitian hB'.isSelfAdjoint.exp.isHermitian hAB'.exp
  have hsquare (X : Matrix X X ℂ) :
      NormedSpace.exp ((a : ℂ) • X) * NormedSpace.exp ((a : ℂ) • X) =
        NormedSpace.exp (((2 * a : ℝ) : ℂ) • X) := by
    rw [← Matrix.exp_add_of_commute ((a : ℂ) • X) ((a : ℂ) • X) (Commute.refl _)]
    congr 1
    rw [two_mul, Complex.ofReal_add, add_smul]
  rw [hsquare A, hsquare B] at h
  rw [smul_add, Matrix.exp_add_of_commute ((a : ℂ) • A) ((a : ℂ) • B) hAB']
  linarith

end Matrix
