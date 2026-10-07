/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.UnitaryEvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Consumers of actual global unitary evolution and its uniqueness. -/

open scoped Matrix Matrix.Norms.L2Operator NNReal
open MatrixEvolution

namespace MatrixUnitaryEvolutionTest

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Independently varying sine and cosine coefficients are allowed. The two
-- Hermitian matrices need not commute, and no solution is supplied as an input.
example (B C : Matrix n n ℂ) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • (Real.sin t • B + Real.cos t • C)) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup n ℂ) ∧
      ∀ V : ℝ → Matrix n n ℂ, V 0 = 1 →
        (∀ t, HasDerivAt V
          ((Complex.I • (Real.sin t • B + Real.cos t • C)) * V t) t) → V = U := by
  have hsin (t : ℝ) : ‖Real.sin t • B‖ ≤ ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg B)
  have hcos (t : ℝ) : ‖Real.cos t • C‖ ≤ ‖C‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (norm_nonneg C)
  apply exists_unique_unitary_solution (fun t ↦ Real.sin t • B + Real.cos t • C)
    ((Real.contDiff_sin.smul contDiff_const).add
      (Real.contDiff_cos.smul contDiff_const))
    (fun t ↦ (hB.smul (IsSelfAdjoint.all (Real.sin t))).add
      (hC.smul (IsSelfAdjoint.all (Real.cos t)))) (‖B‖₊ + ‖C‖₊)
  intro t
  change ‖Real.sin t • B + Real.cos t • C‖ ≤ ‖B‖ + ‖C‖
  exact (norm_add_le _ _).trans (add_le_add (hsin t) (hcos t))

-- The uniqueness clause applies to every solution, without assuming that the
-- competing path is unitary. At M = 0 it identifies it with the constant identity.
example (V : ℝ → Matrix n n ℂ) (hV0 : V 0 = 1)
    (hV : ∀ t, HasDerivAt V 0 t) : V = fun _ ↦ 1 := by
  obtain ⟨U, _, _, _, hUnique⟩ := exists_unique_unitary_solution
    (fun _ ↦ (0 : Matrix n n ℂ)) contDiff_const
    (fun _ ↦ Matrix.isHermitian_zero) 0 (fun _ ↦ by simp)
  have hVeq : V = U := hUnique V hV0 (fun t ↦ by simpa using hV t)
  have hIdentity : (fun _ : ℝ ↦ (1 : Matrix n n ℂ)) = U :=
    hUnique (fun _ ↦ 1) rfl
      (fun t ↦ by simpa using hasDerivAt_const t (1 : Matrix n n ℂ))
  exact hVeq.trans hIdentity.symm

-- On the zero-dimensional Hilbert space every generator meets the hypotheses;
-- existence, unitarity, and uniqueness still use the same capstone theorem.
example (G : ℝ → Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ U : ℝ → Matrix (Fin 0) (Fin 0) ℂ, U 0 = 1 ∧
      (∀ t, HasDerivAt U ((Complex.I • G t) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (Fin 0) ℂ) ∧
      ∀ V : ℝ → Matrix (Fin 0) (Fin 0) ℂ, V 0 = 1 →
        (∀ t, HasDerivAt V ((Complex.I • G t) * V t) t) → V = U := by
  have hG : G = fun _ ↦ 0 := Subsingleton.elim _ _
  rw [hG]
  exact exists_unique_unitary_solution (fun _ ↦ 0) contDiff_const
    (fun _ ↦ Matrix.isHermitian_zero) 0 (fun _ ↦ by simp)

end MatrixUnitaryEvolutionTest

set_option linter.hashCommand false

/--
info: 'MatrixEvolution.exists_unique_unitary_solution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.exists_unique_unitary_solution
