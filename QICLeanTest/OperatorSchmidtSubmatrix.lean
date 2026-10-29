/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtSubmatrix

/-!
# Applications and axiom checks for operator Schmidt coordinate restrictions
-/

open scoped BigOperators Kronecker

/-- info:
'Matrix.operatorSchmidtRank_submatrix_prod_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_submatrix_prod_le

/-- info:
'Matrix.operatorSchmidtRank_fix_outer_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_fix_outer_le

-- No injectivity is required, even if every coordinate is repeated.
example (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.operatorSchmidtRank (M.submatrix
      (Prod.map (fun _ : Fin 3 ↦ (0 : Fin 2)) (fun _ : Fin 4 ↦ (0 : Fin 2)))
      (Prod.map (fun _ : Fin 3 ↦ (1 : Fin 2)) (fun _ : Fin 4 ↦ (1 : Fin 2)))) ≤
        Matrix.operatorSchmidtRank M :=
  Matrix.operatorSchmidtRank_submatrix_prod_le M _ _ _ _

-- Empty retained factors are included.
example (M : Matrix ((Fin 1 × Fin 0) × (Fin 0 × Fin 1))
    ((Fin 1 × Fin 0) × (Fin 0 × Fin 1)) ℂ) :
    Matrix.operatorSchmidtRank (M.submatrix
      (fun x : Fin 0 × Fin 0 ↦ (((0 : Fin 1), x.1), (x.2, (0 : Fin 1))))
      (fun x : Fin 0 × Fin 0 ↦ (((0 : Fin 1), x.1), (x.2, (0 : Fin 1))))) ≤
        Matrix.operatorSchmidtRank M :=
  Matrix.operatorSchmidtRank_fix_outer_le M 0 0 0 0
