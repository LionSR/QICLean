/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtPrescribedFactors

/-!
# Applications and axiom checks for operator Schmidt factor selection
-/

open scoped BigOperators Kronecker

/-- info:
'Matrix.exists_left_factors_of_operatorBlock_mem_span' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.exists_left_factors_of_operatorBlock_mem_span

/-- info:
'Matrix.exists_right_factors_of_left_blocks_mem_span' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.exists_right_factors_of_left_blocks_mem_span

-- The empty prescribed family gives the zero operator without padding factors.
example : ∃ A : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ,
    (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      ∑ t, A t ⊗ₖ (Fin.elim0 t : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact Matrix.exists_left_factors_of_operatorBlock_mem_span 0 Fin.elim0
    (fun _ _ ↦ Submodule.zero_mem _)
