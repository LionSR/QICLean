/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TripartitePolynomialSchmidtRank

/-! # Axiom guard and boundary applications for a tripartite coefficient -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.operatorSchmidtRank_middle_coeff_coeff_pow_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_middle_coeff_coeff_pow_le

open scoped Kronecker
noncomputable section
namespace Matrix

-- Boundary applications.
-- k=0: both counts vanish, with no hypothesis on either crossing matrix.
example {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (AL : Matrix l l ℂ) (AM : Matrix m m ℂ) (AR : Matrix n n ℂ)
    (U : Matrix (l × m) (l × m) ℂ)
    (V : Matrix (m × n) (m × n) ℂ) :=
  operatorSchmidtRank_middle_coeff_coeff_pow_le AL AM AR U V
    (rU := operatorSchmidtRank U) (rV := operatorSchmidtRank V)
    (k := 0) (i := 0) (j := 0) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)

-- An empty left factor is permitted at positive power.
example {m n : Type*} [Fintype m] [Fintype n]
    (AL : Matrix Empty Empty ℂ) (AM : Matrix m m ℂ) (AR : Matrix n n ℂ)
    (U : Matrix (Empty × m) (Empty × m) ℂ)
    (V : Matrix (m × n) (m × n) ℂ) :=
  operatorSchmidtRank_middle_coeff_coeff_pow_le AL AM AR U V
    (rU := operatorSchmidtRank U) (rV := operatorSchmidtRank V)
    (k := 2) (i := 1) (j := 1) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide)

end Matrix
