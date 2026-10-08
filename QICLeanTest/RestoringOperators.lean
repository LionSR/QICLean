/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringOperators

/-! Finite consumers detecting omission of zero-eigenvalue columns and conjugation errors. -/

open Matrix Entropy
open scoped BigOperators Kronecker

/-- The column indexed by the zero eigenvalue survives the full-basis sum. -/
example :
    columnOperator {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false 1) (Pi.single false 1)
      (1 : Matrix (Bool × Fin 1) (Bool × Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
      ((false, true), (false, 0)) ((false, false), (true, 0)) = 1 := by
  simp [columnOperator, restoringWeight, basisColumn, vecMulVec_apply,
    Matrix.smul_apply, Matrix.sum_apply, kroneckerMap_apply, Pi.single_apply,
    Matrix.single_apply, Fintype.sum_bool]

/-- A complex blank phase is conjugated in the input bra. -/
example :
    columnOperator {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false 1) (Pi.single false Complex.I)
      (1 : Matrix (Bool × Fin 1) (Bool × Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
      ((false, true), (false, 0)) ((false, false), (true, 0)) = -Complex.I := by
  simp [columnOperator, restoringWeight, basisColumn, vecMulVec_apply,
    Matrix.smul_apply, Matrix.sum_apply, kroneckerMap_apply, Pi.single_apply,
    Matrix.single_apply, Fintype.sum_bool]

/-- Empty selections produce zero even if all probabilities vanish. -/
example (s x : Bool → ℂ) (Q : Matrix (Bool × Fin 2) (Bool × Fin 2) ℂ)
    (T : Matrix (Fin 2) (Fin 2) ℂ) :
    restoringOperator ∅ (fun _ ↦ 0) s x Q T = 0 := by
  simp [restoringOperator]

/--
info: 'Entropy.restoringOperator_gram' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.restoringOperator_gram

/--
info: 'Entropy.columnOperator_gram' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.columnOperator_gram

/--
info: 'Entropy.restoringGram_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.restoringGram_posSemidef
