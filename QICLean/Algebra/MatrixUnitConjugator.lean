/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.Ring

/-!
# Matrix-unit conjugators

A column obtained from the images of matrix units intertwines an inner action.
The construction requires no choice of a continuous family of conjugating matrices.
-/

open scoped Matrix

namespace Matrix

variable {D : ℕ}

/-- A matrix-unit column extracts a conjugator near a chosen invertible
matrix. This is an auxiliary construction for the virtual continuity
argument of arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
def matrixUnitConjugator
    (α : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (X₀ : Matrix (Fin D) (Fin D) ℂ) (a : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => (α (single j a 1) * X₀) i a

/-- If an action is conjugation by an invertible matrix, its matrix-unit
conjugator is a scalar multiple of that matrix. Source context:
arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem matrixUnitConjugator_eq_smul
    (α : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (X₀ : Matrix (Fin D) (Fin D) ℂ) (a : Fin D) (Y : GL (Fin D) ℂ)
    (hα : ∀ M, α M = Y * M * Y⁻¹) :
    matrixUnitConjugator α X₀ a =
      ((((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * X₀) a a) •
        (Y : Matrix (Fin D) (Fin D) ℂ) := by
  ext i j
  simp [matrixUnitConjugator, hα, Matrix.mul_apply,
    Matrix.single, mul_comm, mul_ite, ite_and, Finset.mul_sum, mul_assoc]

/-- The matrix-unit conjugator intertwines every matrix whenever the given
action is inner. Source context: arXiv:1010.3732, Section II.F.2,
lines 1000–1018. -/
theorem matrixUnitConjugator_intertwines
    (α : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (X₀ : Matrix (Fin D) (Fin D) ℂ) (a : Fin D) (Y : GL (Fin D) ℂ)
    (hα : ∀ M, α M = Y * M * Y⁻¹) (M : Matrix (Fin D) (Fin D) ℂ) :
    α M * matrixUnitConjugator α X₀ a = matrixUnitConjugator α X₀ a * M := by
  rw [matrixUnitConjugator_eq_smul α X₀ a Y hα, hα M]
  simp [Matrix.mul_assoc]

end Matrix
