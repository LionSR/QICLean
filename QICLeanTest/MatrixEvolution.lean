/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixEvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Regression consumers for actual global matrix ODE existence. -/

open scoped Matrix.Norms.L2Operator NNReal

namespace MatrixEvolutionTest

variable {n : Type*} [Fintype n] [DecidableEq n]

-- A zero bound is valid, and the initial matrix need not be invertible or unitary.
example (X0 : Matrix n n ℂ) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = X0 ∧ ∀ t, HasDerivAt U 0 t := by
  simpa using MatrixEvolution.exists_solution (fun _ ↦ (0 : Matrix n n ℂ))
    contDiff_const 0 (fun _ ↦ by simp) X0

-- A constant coefficient need not be Hermitian or skew-Hermitian.
example (B X0 : Matrix n n ℂ) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = X0 ∧ ∀ t, HasDerivAt U (B * U t) t := by
  exact MatrixEvolution.exists_solution (fun _ ↦ B) contDiff_const ‖B‖₊
    (fun _ ↦ le_rfl) X0

-- Two arbitrary matrices give a bounded, varying coefficient without a
-- commutativity hypothesis, on the entire real time axis.
example (B C X0 : Matrix n n ℂ) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = X0 ∧
      ∀ t, HasDerivAt U ((Real.sin t • B + Real.cos t • C) * U t) t := by
  have hsin (t : ℝ) : ‖Real.sin t • B‖ ≤ ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg B)
  have hcos (t : ℝ) : ‖Real.cos t • C‖ ≤ ‖C‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (norm_nonneg C)
  apply MatrixEvolution.exists_solution
    (fun t ↦ Real.sin t • B + Real.cos t • C)
    ((Real.contDiff_sin.smul contDiff_const).add
      (Real.contDiff_cos.smul contDiff_const)) (‖B‖₊ + ‖C‖₊) _ X0
  intro t
  change ‖Real.sin t • B + Real.cos t • C‖ ≤ ‖B‖ + ‖C‖
  exact (norm_add_le _ _).trans (add_le_add (hsin t) (hcos t))

-- Empty finite index types require no artificial nontriviality assumption.
example (A : ℝ → Matrix (Fin 0) (Fin 0) ℂ) (X0 : Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ U : ℝ → Matrix (Fin 0) (Fin 0) ℂ,
      U 0 = X0 ∧ ∀ t, HasDerivAt U (A t * U t) t := by
  apply MatrixEvolution.exists_solution A _ 0 _ X0
  · have hA : A = fun _ ↦ 0 := Subsingleton.elim _ _
    rw [hA]
    exact contDiff_const
  · intro t
    have hAt : A t = 0 := Subsingleton.elim _ _
    simp [hAt]

end MatrixEvolutionTest

set_option linter.hashCommand false

/--
info: 'MatrixEvolution.exists_solution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.exists_solution
