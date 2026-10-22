/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PolynomialLinearFactor

/-!
# Exchanging the order of two coefficient markers

Two central polynomial variables mark two designated summands of a generating
polynomial. The same pair of marked counts is obtained in either nesting order,
even when the elements D, U, and V coincide or satisfy algebraic relations.
No commutation assumption on the coefficient semiring is needed.

This identity supports the simultaneous two-cut coefficient family in ALVV,
arXiv:1602.08828v2, Proposition prop:Cheby-AGSP-eff, lines 1324 and 1332.
The ordered-word interpretation is AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 604–617 and 626–635. No locality, rank, spectral, or viability claim is
part of this statement.
-/

namespace Polynomial

/-- Exchanging which distinguished letter is counted by the outer variable
preserves the same ordered-word coefficient. ALVV, arXiv:1602.08828v2,
prop:Cheby-AGSP-eff, lines 1324 and 1332; AKLV, arXiv:1301.1162v1,
l:agsp, lines 604–617 and 626–635. -/
theorem coeff_coeff_pow_two_markers_swap
    {R : Type*} [Semiring R] (D U V : R) (k i j : ℕ) :
    let F : Polynomial (Polynomial R) :=
      C (C D + C V * X) + C (C U) * X
    let G : Polynomial (Polynomial R) :=
      C (C D + C U * X) + C (C V) * X
    ((F ^ k).coeff i).coeff j = ((G ^ k).coeff j).coeff i := by
  dsimp only
  induction k generalizing i j with
  | zero =>
    cases i <;> cases j <;> simp [coeff_one]
  | succ k ih =>
    cases i <;> cases j <;>
      simp only [pow_succ', coeff_C_add_C_mul_X_mul_succ, mul_coeff_zero,
        coeff_add, coeff_C_mul, coeff_C_zero, coeff_X_zero, mul_zero, add_zero,
        ih, add_assoc, add_comm, add_left_comm]

end Polynomial
