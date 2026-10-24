/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FiniteMonomialInterpolation

/-! # Kernel dependencies of finite monomial interpolation -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'MvPolynomial.exists_monomial_evaluation_recovery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.exists_monomial_evaluation_recovery

/-- info:
'MvPolynomial.monomial_evaluation_recovery_smul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.monomial_evaluation_recovery_smul
