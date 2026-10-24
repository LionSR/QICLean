/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients after multiplication by a linear polynomial

Left multiplication by a polynomial with constant coefficient D and linear
coefficient T gives the two-term coefficient recurrence. The coefficient
semiring need not be commutative, and all products retain their order.

This is the elementary recurrence used in the ordered-gap argument of AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–653.
-/

namespace Polynomial

/-- The successor coefficient after left multiplication by a polynomial of
degree at most one. This is the coefficient recurrence used in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–653. -/
theorem coeff_C_add_C_mul_X_mul_succ
    {R : Type*} [Semiring R] (D T : R) (P : Polynomial R) (n : ℕ) :
    ((C D + C T * X) * P).coeff (n + 1) =
      D * P.coeff (n + 1) + T * P.coeff n := by
  rw [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_mul]

end Polynomial
