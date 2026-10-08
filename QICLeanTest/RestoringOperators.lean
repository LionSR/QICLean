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
    Matrix.single_apply]

/-- A complex blank phase is conjugated in the input bra. -/
example :
    columnOperator {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false 1) (Pi.single false Complex.I)
      (1 : Matrix (Bool × Fin 1) (Bool × Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
      ((false, true), (false, 0)) ((false, false), (true, 0)) = -Complex.I := by
  simp [columnOperator, restoringWeight, basisColumn, vecMulVec_apply,
    Matrix.smul_apply, Matrix.sum_apply, kroneckerMap_apply, Pi.single_apply,
    Matrix.single_apply]

/-- The spectator permutation puts `e` last and retains every physical coordinate. -/
example : restoringAncillaGrouping (Y := Fin 1)
    ((false, true), (false, 0)) = ((false, (false, 0)), true) := rfl

/-- Empty selections produce zero even if all probabilities vanish. -/
example (s x : Bool → ℂ) (Q : Matrix (Bool × Fin 2) (Bool × Fin 2) ℂ)
    (T : Matrix (Fin 2) (Fin 2) ℂ) :
    restoringOperator ∅ (fun _ ↦ 0) s x Q T = 0 := by
  simp [restoringOperator]
