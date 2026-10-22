/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.CommutingPolynomialSchmidtRank

/-! # Axiom check and concrete boundary applications for coefficient rank -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators Kronecker

/-- info:
'Matrix.operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le

namespace Matrix

private abbrev OneFactor := Matrix (Unit × Unit) (Unit × Unit) ℂ

private noncomputable def unitGapPolynomial (T : OneFactor) : Polynomial OneFactor :=
  Polynomial.C (1 + 1) + Polynomial.C T * Polynomial.X

private theorem unit_rank_le_one (X : OneFactor) : operatorSchmidtRank X ≤ 1 := by
  simpa [operatorSchmidtRank, Module.finrank_matrix] using (LinearMap.finrank_range_le (operatorSchmidtMap X))

private theorem unit_zero_rank : operatorSchmidtRank (0 : OneFactor) ≤ 0 :=
  operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨Fin.elim0, Fin.elim0, by simp⟩

-- Both local dimensions are one. The ordinary coefficient has no distinguished letters.
example (m : ℕ) : operatorSchmidtRank ((unitGapPolynomial 0 ^ m).coeff 0) ≤ m + 1 := by
  simpa [unitGapPolynomial] using
    operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le (1 : OneFactor) 1 0
      (Commute.refl _) (unit_rank_le_one _) (unit_rank_le_one _) unit_zero_rank m 0

-- The same nonempty system has distinguished letter I and no ordinary letters.
example (k : ℕ) : operatorSchmidtRank ((unitGapPolynomial 1 ^ k).coeff k) ≤ 1 := by
  simpa [unitGapPolynomial] using
    operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le (1 : OneFactor) 1 1
      (Commute.refl _) (unit_rank_le_one _) (unit_rank_le_one _) (unit_rank_le_one _) 0 k

-- Rank bound zero and a positive distinguished-letter count: the actual coefficient vanishes.
example (m k : ℕ) :
    operatorSchmidtRank ((unitGapPolynomial 0 ^ (m + (k + 1))).coeff (k + 1)) ≤ 0 := by
  simpa [unitGapPolynomial] using
    operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le (1 : OneFactor) 1 0
      (Commute.refl _) (unit_rank_le_one _) (unit_rank_le_one _) unit_zero_rank m (k + 1)

end Matrix
