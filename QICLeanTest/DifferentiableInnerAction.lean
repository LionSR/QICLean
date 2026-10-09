/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DifferentiableInnerAction
import QICLean.Analysis.HermitianUnitaryPath
import Mathlib.Tactic.FunProp

/-! Regressions for the matrix-unit section and Hermitian derivative extraction. -/

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace DifferentiableInnerActionTest

example {D : ℕ} [NeZero D] (a : Fin D) :
    matrixUnitConjugator (fun M : Matrix (Fin D) (Fin D) ℂ => M) 1 a = 1 := by
  ext i j
  simp [matrixUnitConjugator, Matrix.single, Matrix.one_apply, eq_comm]

-- The identity action needs no regularity premise on a chosen gauge.
example {D : ℕ} [NeZero D] :
    ∃ H : Matrix (Fin D) (Fin D) ℂ, H.IsHermitian ∧
      ∀ M, HasDerivAt (fun _ : ℝ => M) (Complex.I • (H * M - M * H)) 0 := by
  apply exists_hermitian_generator_of_differentiable_innerAction
  · exact fun M => differentiableAt_const M
  · exact fun _ => rfl
  · exact fun _ => ⟨1, by simp, fun _ => by simp⟩

-- A conjugation path gives the same derivative even if the extracted
-- Hermitian generator differs from K by a scalar.
example {D : ℕ} [NeZero D] (K : Matrix (Fin D) (Fin D) ℂ) (hK : K.IsHermitian) :
    ∃ H : Matrix (Fin D) (Fin D) ℂ, H.IsHermitian ∧
      ∀ M, HasDerivAt
        (fun t => hermitianUnitaryPath K t * M * (hermitianUnitaryPath K t)ᴴ)
        (Complex.I • (H * M - M * H)) 0 := by
  apply exists_hermitian_generator_of_differentiable_innerAction
  · intro M
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • K) 0
    have hp : DifferentiableAt ℝ (hermitianUnitaryPath K) 0 := by
      apply differentiableAt_pi.mpr
      intro i
      apply differentiableAt_pi.mpr
      intro j
      simpa [hermitianUnitaryPath] using
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j).differentiableAt
    exact (hp.mul_const M).mul hp.star
  · intro M
    simp
  · exact fun t => ⟨hermitianUnitaryPath K t,
      hermitianUnitaryPath_mul_conjTranspose K hK t, fun _ => rfl⟩

end DifferentiableInnerActionTest

/--
info: 'Matrix.matrixUnitConjugator_eq_smul' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrixUnitConjugator_eq_smul

/--
info: 'Matrix.matrixUnitConjugator_intertwines' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrixUnitConjugator_intertwines

/--
info: 'Matrix.exists_hermitian_generator_of_differentiable_innerAction' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_hermitian_generator_of_differentiable_innerAction
