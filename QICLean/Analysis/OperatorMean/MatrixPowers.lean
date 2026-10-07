/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcLogAdditive
import QICLean.Analysis.MatrixSqrt
import QICLean.Analysis.PosSemidefCommute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Real powers of positive definite matrices

This file collects the elementary identities for real powers of positive
definite complex matrices used by the weighted geometric mean: positivity of
the powers, the exponent law, cancellation of a power against its negative,
scalar homogeneity, and the factorization of a power of a product of
commuting positive definite matrices.

## Main results

* `Matrix.PosDef.rpow` — a real power of a positive definite matrix is
  positive definite.
* `Matrix.PosDef.rpow_mul_rpow` — the exponent law `A ^ r * A ^ s = A ^ (r + s)`.
* `Matrix.PosDef.smul_rpow` — `(c • A) ^ r = c ^ r • A ^ r` for `c > 0`.
* `Matrix.PosDef.commute_rpow` — real powers of commuting positive definite
  matrices commute.
* `Matrix.PosDef.mul_rpow_of_commute` — `(A * B) ^ r = A ^ r * B ^ r` for
  commuting positive definite `A` and `B`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace PosDef

variable {A B : Matrix n n ℂ}

/-- A real power of a positive definite matrix is positive definite. -/
theorem rpow (hA : A.PosDef) (r : ℝ) : (A ^ r).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.rpow A r hA.isStrictlyPositive)

/-- A real power of a positive definite matrix is Hermitian. -/
theorem rpow_isHermitian (hA : A.PosDef) (r : ℝ) : (A ^ r).IsHermitian :=
  (hA.rpow r).isHermitian

/-- The conjugate transpose of a real power of a positive definite matrix is
itself. -/
@[simp] theorem star_rpow (hA : A.PosDef) (r : ℝ) : star (A ^ r) = A ^ r :=
  (hA.rpow_isHermitian r).eq

/-- The exponent law for real powers of a positive definite matrix. -/
theorem rpow_mul_rpow (hA : A.PosDef) (r s : ℝ) : A ^ r * A ^ s = A ^ (r + s) :=
  (CFC.rpow_add hA.isUnit).symm

/-- The zeroth real power of a positive definite matrix is the identity. -/
@[simp] theorem rpow_zero (hA : A.PosDef) : A ^ (0 : ℝ) = 1 :=
  CFC.rpow_zero A hA.posSemidef.nonneg

/-- The first real power of a positive definite matrix is the matrix. -/
@[simp] theorem rpow_one (hA : A.PosDef) : A ^ (1 : ℝ) = A :=
  CFC.rpow_one A hA.posSemidef.nonneg

/-- A real power cancels against its negative. -/
theorem rpow_mul_rpow_neg (hA : A.PosDef) (r : ℝ) : A ^ r * A ^ (-r) = 1 := by
  rw [hA.rpow_mul_rpow, add_neg_cancel, hA.rpow_zero]

/-- A negative real power cancels against the positive one. -/
theorem rpow_neg_mul_rpow (hA : A.PosDef) (r : ℝ) : A ^ (-r) * A ^ r = 1 := by
  rw [hA.rpow_mul_rpow, neg_add_cancel, hA.rpow_zero]

/-- The square of the positive square root is the matrix. -/
theorem rpow_half_mul_rpow_half (hA : A.PosDef) :
    A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
  rw [hA.rpow_mul_rpow]; norm_num [hA.rpow_one]

/-- Iterated real powers multiply exponents. -/
theorem rpow_rpow (hA : A.PosDef) (r s : ℝ) : (A ^ r) ^ s = A ^ (r * s) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [hA.rpow_zero, CFC.one_rpow]
  · exact CFC.rpow_rpow A r s hr hA.isStrictlyPositive

/-- Scalar homogeneity of real powers: `(c • A) ^ r = c ^ r • A ^ r` for a positive real
scalar `c`. -/
theorem smul_rpow (hA : A.PosDef) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (c • A) ^ r = c ^ r • A ^ r := by
  have hcA : (c • A).PosDef := hA.smul hc
  rw [CFC.rpow_eq_cfc_real hcA.posSemidef.nonneg, CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  rw [← cfc_comp_smul c (fun x : ℝ ↦ x ^ r) A ((A.finite_real_spectrum.image _).continuousOn _),
    ← cfc_smul (c ^ r) (fun x : ℝ ↦ x ^ r) A (A.finite_real_spectrum.continuousOn _)]
  refine cfc_congr fun x hx ↦ ?_
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.posSemidef.nonneg hx
  simp [smul_eq_mul, Real.mul_rpow hc.le hx0]

/-- Real powers of commuting positive definite matrices commute. -/
theorem commute_rpow (hA : A.PosDef) (hB : B.PosDef) (hAB : Commute A B) (r s : ℝ) :
    Commute (A ^ r) (B ^ s) := by
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, CFC.rpow_eq_cfc_real hB.posSemidef.nonneg]
  exact Commute.cfc_real (Commute.cfc_real hAB.symm _).symm _

/-- A real power of a positive definite matrix commutes with every matrix commuting with
the original matrix. -/
theorem commute_rpow_left (hA : A.PosDef) {X : Matrix n n ℂ} (hAX : Commute A X) (r : ℝ) :
    Commute (A ^ r) X := by
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact Commute.cfc_real hAX _

omit [DecidableEq n] in
/-- The product of commuting positive definite matrices is positive definite. -/
theorem mul_of_commute (hA : A.PosDef) (hB : B.PosDef) (hAB : Commute A B) :
    (A * B).PosDef := by
  classical
  exact (hA.posSemidef.mul_of_commute hB.posSemidef hAB.eq).posDef_iff_isUnit.mpr
    (hA.isUnit.mul hB.isUnit)

/-- A real power of a product of commuting positive definite matrices is the product of
the real powers. -/
theorem mul_rpow_of_commute (hA : A.PosDef) (hB : B.PosDef) (hAB : Commute A B) (r : ℝ) :
    (A * B) ^ r = A ^ r * B ^ r := by
  have hAB' : (A * B).PosDef := hA.mul_of_commute hB hAB
  have hr : (A ^ r * B ^ r).PosDef :=
    (hA.rpow r).mul_of_commute (hB.rpow r) (hA.commute_rpow hB hAB r r)
  have hlog : CFC.log ((A * B) ^ r) = CFC.log (A ^ r * B ^ r) := by
    rw [hAB'.cfc_log_rpow, cfc_log_mul hA hB hAB,
      cfc_log_mul (hA.rpow r) (hB.rpow r) (hA.commute_rpow hB hAB r r),
      hA.cfc_log_rpow, hB.cfc_log_rpow, smul_add]
  rw [← CFC.exp_log ((A * B) ^ r) (hAB'.rpow r).isStrictlyPositive,
    ← CFC.exp_log (A ^ r * B ^ r) hr.isStrictlyPositive, hlog]

end PosDef

end Matrix
