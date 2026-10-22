/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PolynomialTwoMarkerPower

/-! # Axiom audit and ordered two-marker coefficient applications -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Polynomial.coeff_C_add_C_mul_X_mul_succ'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.coeff_C_add_C_mul_X_mul_succ

/-- info:
'Polynomial.coeff_coeff_pow_two_markers_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.coeff_coeff_pow_two_markers_swap

namespace Polynomial

-- Zero power is included for all coefficient indices, including D=U=V=0.
example {R : Type*} [Semiring R] (D U V : R) (i j : ℕ) :=
  coeff_coeff_pow_two_markers_swap D U V 0 i j

-- The mixed degree-two coefficient retains both operator orders.
example {R : Type*} [Semiring R] (D U V : R) :
    let F : Polynomial (Polynomial R) :=
      C (C D + C V * X) + C (C U) * X
    ((F ^ 2).coeff 1).coeff 1 = U * V + V * U := by
  simp only [pow_succ', add_mul, mul_assoc, coeff_add, coeff_C_mul,
    coeff_X_mul, pow_zero, coeff_C, mul_one]
  simp [coeff_X, coeff_one, add_comm]

end Polynomial
