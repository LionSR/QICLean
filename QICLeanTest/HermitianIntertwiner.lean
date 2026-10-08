/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.HermitianIntertwiner
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Regressions for rectangular and empty-support Hermitian intertwiners. -/
open scoped Matrix
open Matrix

-- Rectangular zero maps retain the zero-on-kernel conclusion.
example (L : Matrix (Fin 2) (Fin 2) ℂ) (hL : L.IsHermitian) :
    ∃ K : Matrix (Fin 5) (Fin 5) ℂ,
      K.IsHermitian ∧ (0 : Matrix (Fin 2) (Fin 5) ℂ) * K = L * (0 : Matrix (Fin 2) (Fin 5) ℂ) ∧
      ∀ v : Fin 5 → ℂ, (0 : Matrix (Fin 2) (Fin 5) ℂ).mulVec v = 0 → K.mulVec v = 0 := by
  apply exists_hermitian_intertwiner_of_commute_mul_conjTranspose _ L hL
  simp [Commute, SemiconjBy]

-- Both independent empty-index directions remain valid.
example (L : Matrix (Fin 0) (Fin 0) ℂ) (hL : L.IsHermitian)
    (F : Matrix (Fin 0) (Fin 3) ℂ) :
    ∃ K : Matrix (Fin 3) (Fin 3) ℂ, K.IsHermitian ∧ F * K = L * F := by
  apply (commute_mul_conjTranspose_iff_exists_hermitian_intertwiner F L hL).mp
  exact Subsingleton.elim _ _

example (L : Matrix (Fin 3) (Fin 3) ℂ) (hL : L.IsHermitian)
    (F : Matrix (Fin 3) (Fin 0) ℂ) :
    ∃ K : Matrix (Fin 0) (Fin 0) ℂ, K.IsHermitian ∧ F * K = L * F := by
  apply (commute_mul_conjTranspose_iff_exists_hermitian_intertwiner F L hL).mp
  change L * (F * Fᴴ) = (F * Fᴴ) * L
  have hFF : F * Fᴴ = 0 := by ext; simp [Matrix.mul_apply]
  simp [hFF]

namespace HermitianIntertwinerTest
private def F : Matrix (Fin 2) (Fin 3) ℂ := !![1, 0, 0; 0, 0, 0]
private def L : Matrix (Fin 2) (Fin 2) ℂ := !![2, 0; 0, 3]

-- Singular left Gram and a two-dimensional unused physical subspace.
example : ∃ K : Matrix (Fin 3) (Fin 3) ℂ,
    K.IsHermitian ∧ F * K = L * F ∧
    ∀ v : Fin 3 → ℂ, F.mulVec v = 0 → K.mulVec v = 0 := by
  apply exists_hermitian_intertwiner_of_commute_mul_conjTranspose F L
  · ext a b
    fin_cases a <;> fin_cases b <;> norm_num [L, Matrix.conjTranspose_apply]
  · change L * (F * Fᴴ) = (F * Fᴴ) * L
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [F, L, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
        Matrix.vecMul, dotProduct]
end HermitianIntertwinerTest

/--
info: 'Matrix.commute_mul_conjTranspose_of_hermitian_intertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.commute_mul_conjTranspose_of_hermitian_intertwiner

/--
info: 'Matrix.isHermitian_conjTranspose_mul_mul_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isHermitian_conjTranspose_mul_mul_mul

/--
info: 'Matrix.mul_supportedHermitianLift' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.mul_supportedHermitianLift

/--
info: 'Matrix.supportedHermitianLift_mulVec_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.supportedHermitianLift_mulVec_eq_zero

/--
info: 'Matrix.PosSemidef.commute_supportInv' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.commute_supportInv

/--
info: 'Matrix.exists_hermitian_intertwiner_of_commute_mul_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_hermitian_intertwiner_of_commute_mul_conjTranspose

/--
info: 'Matrix.commute_mul_conjTranspose_iff_exists_hermitian_intertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.commute_mul_conjTranspose_iff_exists_hermitian_intertwiner
