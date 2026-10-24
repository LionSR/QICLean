/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.SchmidtRankAction

/-!
# Axiom check and boundary cases for Schmidt rank after an operator acts

The applications cover the zero vector and either tensor factor being empty.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped Matrix

/-- info:
'Matrix.schmidtRank_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.schmidtRank_mulVec_le

namespace Matrix

/-- Arbitrary operators preserve the zero Schmidt rank of the zero vector. -/
private theorem zero_vector_boundary
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ) :
    schmidtRank (K *ᵥ (fun _ : m × n ↦ (0 : ℂ))) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [schmidtRank_zero, Nat.mul_zero] using
    schmidtRank_mulVec_le K (fun _ : m × n ↦ (0 : ℂ))

/-- The left tensor factor may be empty. -/
private theorem empty_left_boundary
    {n : Type*} [Fintype n]
    (K : Matrix (Empty × n) (Empty × n) ℂ) (ψ : Empty × n → ℂ) :
    schmidtRank (K *ᵥ ψ) = 0 := by
  have hψ : ψ = (fun _ : Empty × n ↦ (0 : ℂ)) :=
    funext fun p ↦ Empty.elim p.1
  rw [hψ]
  exact zero_vector_boundary K

/-- The right tensor factor may be empty. -/
private theorem empty_right_boundary
    {m : Type*} [Fintype m]
    (K : Matrix (m × Empty) (m × Empty) ℂ) (ψ : m × Empty → ℂ) :
    schmidtRank (K *ᵥ ψ) = 0 := by
  have hψ : ψ = (fun _ : m × Empty ↦ (0 : ℂ)) :=
    funext fun p ↦ Empty.elim p.2
  rw [hψ]
  exact zero_vector_boundary K

end Matrix
