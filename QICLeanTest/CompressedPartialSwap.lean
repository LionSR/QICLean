/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CompressedPartialSwap

/-! Regression checks for physical-buffer partial-swap compression. -/

open scoped Matrix Kronecker Matrix.Norms.L2Operator
open Matrix

namespace CompressedPartialSwapTest

-- Unequal factors make the swapped and preserved coordinates distinguishable.
example : Equiv.partialSwap (Fin 2) (Fin 3) ((0, 1), (1, 2)) = ((1, 1), (0, 2)) := rfl

-- A complex entangled embedding has a strictly contractive compression.
noncomputable def complexEmbedding : Matrix (Bool × Bool) Unit ℂ :=
  Matrix.of fun p _ => if p = (false, false) then 3 / 5 else
    if p = (true, true) then 4 * Complex.I / 5 else 0

theorem complexEmbedding_isometry : complexEmbeddingᴴ * complexEmbedding = 1 := by
  ext i j
  cases i
  cases j
  norm_num [complexEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_bool, map_ofNat, Complex.ext_iff]

example : ‖compressedPartialSwap complexEmbedding‖ ≤ 1 :=
  norm_compressedPartialSwap_le_one complexEmbedding_isometry

example : compressedPartialSwap complexEmbedding =
    (337 / 625 : ℂ) • (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ) := by
  rw [compressedPartialSwap, Matrix.mul_assoc, partialSwap, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  rcases i with ⟨⟨⟩, ⟨⟩⟩
  rcases j with ⟨⟨⟩, ⟨⟩⟩
  norm_num [complexEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, map_ofNat, Complex.ext_iff]

-- An empty auxiliary factor is permitted, and its swap has norm zero.
example : ‖partialSwap Empty Bool‖ = 0 := by
  have h : partialSwap Empty Bool = 0 := Subsingleton.elim _ _
  rw [h, norm_zero]

-- An empty original register needs no nonempty hypothesis hidden in the norm bound.
example (V : Matrix (Bool × Bool) Empty ℂ) : ‖compressedPartialSwap V‖ ≤ 1 := by
  apply norm_compressedPartialSwap_le_one
  exact Subsingleton.elim _ _

-- Exact transport retains both arbitrary input vectors and a physical reference swap.
example (V : Matrix (Bool × Fin 3) (Fin 2) ℂ)
    (x y : ((Bool × Unit) × (Bool × Unit)) × (Fin 2 × Fin 2) → ℂ) :
    star ((partialSwap Bool Unit ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
      *ᵥ x) ⬝ᵥ ((1 ⊗ₖ compressedPartialSwap V) *ᵥ y) =
      star ((1 ⊗ₖ (V ⊗ₖ V)) *ᵥ x) ⬝ᵥ
        ((partialSwap Bool Unit ⊗ₖ partialSwap Bool (Fin 3)) *ᵥ
          ((1 ⊗ₖ (V ⊗ₖ V)) *ᵥ y)) :=
  compressedPartialSwap_left_overlap V (partialSwap_isHermitian Bool Unit) x y

end CompressedPartialSwapTest

/--
info: 'Equiv.partialSwap' does not depend on any axioms
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Equiv.partialSwap

/--
info: 'Equiv.partialSwap_apply' depends on axioms:
[Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Equiv.partialSwap_apply

/--
info: 'Equiv.partialSwap_symm' does not depend on any axioms
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Equiv.partialSwap_symm

/--
info: 'Equiv.partialSwap_mul_self' depends on axioms:
[Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Equiv.partialSwap_mul_self

/--
info: 'Matrix.partialSwap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap

/--
info: 'Matrix.partialSwap_apply' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_apply

/--
info: 'Matrix.partialSwap_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_mulVec

/--
info: 'Matrix.partialSwap_isHermitian' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_isHermitian

/--
info: 'Matrix.partialSwap_mul_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_mul_self

/--
info: 'Matrix.partialSwap_mem_unitaryGroup' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_mem_unitaryGroup

/--
info: 'Matrix.norm_partialSwap_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_partialSwap_le_one

/--
info: 'Matrix.partialSwap_kronecker_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_kronecker_mulVec

/--
info: 'Matrix.partialSwap_one_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.partialSwap_one_mulVec

/--
info: 'Matrix.kronecker_self_conjTranspose_mul_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.kronecker_self_conjTranspose_mul_self

/--
info: 'Matrix.compressedPartialSwap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.compressedPartialSwap

/--
info: 'Matrix.compressedPartialSwap_isHermitian' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.compressedPartialSwap_isHermitian

/--
info: 'Matrix.norm_conjTranspose_mul_mul_le_of_isometry' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_conjTranspose_mul_mul_le_of_isometry

/--
info: 'Matrix.norm_compressedPartialSwap_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_compressedPartialSwap_le_one

/--
info: 'Matrix.star_dotProduct_compression' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_dotProduct_compression

/--
info: 'Matrix.star_dotProduct_kronecker_compression' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_dotProduct_kronecker_compression

/--
info: 'Matrix.compressedPartialSwap_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.compressedPartialSwap_overlap

/--
info: 'Matrix.compressedPartialSwap_left_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.compressedPartialSwap_left_overlap
