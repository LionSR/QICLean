/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevFilter

/-! # Kernel dependencies of the Chebyshev filter estimates -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Polynomial.Chebyshev.half_exp_sqrt_le_eval_T'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.Chebyshev.half_exp_sqrt_le_eval_T

/-- info:
'Polynomial.Chebyshev.exists_interval_shrinking_polynomial'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.Chebyshev.exists_interval_shrinking_polynomial
