/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.JordanBlockPower
import Mathlib.Tactic.NoncommRing

/-!
# Operator-norm comparison under similarity

This file formalizes the basis-level comparison used in Wolf's Equation
(8.108).  It deliberately keeps a chosen invertible similarity `A, B`
explicit.  Wolf defines the Jordan condition number `κ_T` as an infimum over
all Jordan bases; replacing the displayed factor below by that infimum requires
an attainment theorem or a separate limiting argument.

Source: Wolf (2012), Chapter 8, Equation (8.108), local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1247--1254.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Equation (8.108) for one chosen similarity `X = A J A⁻¹`, with the
inverse supplied as `B`.

No Jordan-normal-form existence or minimization of the condition factor is
assumed here. -/
theorem l2_opNorm_pow_similarity_bounds
    (A B J X : Matrix ι ι ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (hX : X = A * J * B) (n : ℕ) :
    (‖A‖ * ‖B‖)⁻¹ * ‖J ^ n‖ ≤ ‖X ^ n‖ ∧
      ‖X ^ n‖ ≤ (‖A‖ * ‖B‖) * ‖J ^ n‖ := by
  have hcond : 0 < ‖A‖ * ‖B‖ := by
    have hone : (1 : ℝ) ≤ ‖A‖ * ‖B‖ := by
      calc
        1 = ‖(1 : Matrix ι ι ℂ)‖ := by simp
        _ = ‖A * B‖ := by rw [hAB]
        _ ≤ ‖A‖ * ‖B‖ := l2_opNorm_mul A B
    positivity
  have hpow : X ^ n = A * J ^ n * B := by
    induction n with
    | zero => simpa only [pow_zero, Matrix.mul_one] using hAB.symm
    | succ n ih =>
        rw [pow_succ, ih, hX, pow_succ]
        calc
          A * J ^ n * B * (A * J * B) = A * J ^ n * (B * A) * J * B := by
            simp only [Matrix.mul_assoc]
          _ = A * (J ^ n * J) * B := by
            rw [hBA]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hpow' : J ^ n = B * X ^ n * A := by
    rw [hpow]
    symm
    calc
      B * (A * J ^ n * B) * A = (B * A) * J ^ n * (B * A) := by
        simp only [Matrix.mul_assoc]
      _ = J ^ n := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
  constructor
  · have hle : ‖J ^ n‖ ≤ (‖A‖ * ‖B‖) * ‖X ^ n‖ := by
      calc
        ‖J ^ n‖ = ‖B * X ^ n * A‖ := by rw [hpow']
        _ ≤ ‖B * X ^ n‖ * ‖A‖ := l2_opNorm_mul _ _
        _ ≤ (‖B‖ * ‖X ^ n‖) * ‖A‖ := by
          gcongr
          exact l2_opNorm_mul _ _
        _ = (‖A‖ * ‖B‖) * ‖X ^ n‖ := by ring
    exact (inv_mul_le_iff₀ hcond).2 hle
  · rw [hpow]
    calc
      ‖A * J ^ n * B‖ ≤ ‖A * J ^ n‖ * ‖B‖ := l2_opNorm_mul _ _
      _ ≤ (‖A‖ * ‖J ^ n‖) * ‖B‖ := by
        gcongr
        exact l2_opNorm_mul _ _
      _ = (‖A‖ * ‖B‖) * ‖J ^ n‖ := by ring

end Matrix
