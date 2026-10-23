/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximalOverlap

/-! Boundary applications of the homogeneous maximal-overlap inequality. -/

open scoped Matrix

/-- The zero-rank case is valid even when the second factor is empty. -/
example (C : Matrix (Fin 1) (Fin 0) ℂ) :
    ‖(Cᴴ * (0 : Matrix (Fin 1) (Fin 0) ℂ)).trace‖ ^ 2 ≤
      (Matrix.posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm 0 *
        (((0 : Matrix (Fin 1) (Fin 0) ℂ)ᴴ *
          (0 : Matrix (Fin 1) (Fin 0) ℂ)).trace).re := by
  apply Matrix.normSq_trace_conjTranspose_mul_le_kyFanNorm_mul_trace C 0
  · decide
  · simp

/-- Neither column needs to have unit length. -/
example (C B : Matrix (Fin 2) (Fin 1) ℂ) :
    ‖(Cᴴ * B).trace‖ ^ 2 ≤
      (Matrix.posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm 1 *
        ((Bᴴ * B).trace).re := by
  apply Matrix.normSq_trace_conjTranspose_mul_le_kyFanNorm_mul_trace C B
  · decide
  · simpa using Matrix.rank_le_card_width B

set_option linter.hashCommand false

/-- info:
'Matrix.normSq_trace_conjTranspose_mul_le_kyFanNorm_mul_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.normSq_trace_conjTranspose_mul_le_kyFanNorm_mul_trace
