/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OrderedPolynomialGaps

/-! # Axiom check and endpoint applications of ordered gap collection -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- info:
'Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps

-- The public theorem retains the empty distinguished-letter family.
example {R : Type*} [Semiring R] (D T : R) (m : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ m).coeff 0 = D ^ m := by
  simpa using Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps D T m 0

-- With no D letters there is one all-zero gap tuple, even when T=0.
example {R : Type*} [Semiring R] (D T : R) (k : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ k).coeff k = T ^ k := by
  simpa [Finset.Nat.antidiagonalTuple_zero_right] using
    Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps D T 0 k

-- The first mixed case preserves the order of both products.
example {R : Type*} [Semiring R] (D T : R) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ 2).coeff 1 = D * T + T * D := by
  simpa [Finset.Nat.antidiagonalTuple_two, Finset.Nat.antidiagonal_succ, add_comm] using
    Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps D T 1 1
