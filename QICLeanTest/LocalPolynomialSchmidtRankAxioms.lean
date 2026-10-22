/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.LocalPolynomialSchmidtRank

/-! # Axiom audit and boundary applications for coefficient-rank bounds -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.operatorSchmidtRank_coeff_coeff_pow_left_add_right_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_coeff_coeff_pow_left_add_right_le

open scoped Kronecker
noncomputable section
namespace Matrix
open Classical
variable {l n : Type*} [Fintype l] [Fintype n]

-- The empty word gives the identity, including empty local index types.
example (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ))
    (T : Matrix (l × n) (l × n) ℂ) {r : ℕ} (hT : operatorSchmidtRank T ≤ r) :
    operatorSchmidtRank (1 : Matrix (l × n) (l × n) ℂ) ≤ 1 := by
  simpa using
    operatorSchmidtRank_coeff_coeff_pow_left_add_right_le A B T hT 0 0 0

-- The inferred conclusion specializes the public theorem to an empty left factor.
example (A : Matrix Empty Empty ℂ) (B : Polynomial (Matrix n n ℂ))
    (T : Matrix (Empty × n) (Empty × n) ℂ) {r : ℕ}
    (hT : operatorSchmidtRank T ≤ r) (m j s : ℕ) :=
  operatorSchmidtRank_coeff_coeff_pow_left_add_right_le
    (l := Empty) (n := n) A B T hT m j s

-- A zero crossing operator admits rank bound zero, at positive distinguished frequency.
example (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ)) (m s : ℕ) :=
  operatorSchmidtRank_coeff_coeff_pow_left_add_right_le A B
    (0 : Matrix (l × n) (l × n) ℂ) (r := 0)
    (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨Fin.elim0, Fin.elim0, by simp⟩) m 1 s

end Matrix
