/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.HermitianUnitaryPath
import QICLean.Analysis.KroneckerExponential
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Regressions for complex Hermitian exponential paths and their tensor products. -/
open scoped Matrix Kronecker Topology Matrix.Norms.L2Operator
open Matrix Filter

namespace ContinuousHermitianPathTest
private def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

private theorem pauliY_hermitian : pauliY.IsHermitian := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [pauliY, Matrix.conjTranspose_apply]

private theorem pauliY_nonscalar : ∀ c : ℂ, pauliY ≠ c • 1 := by
  intro c hc
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hc
  norm_num [pauliY, Matrix.one_apply] at h01

example : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ c : ℂ,
    hermitianUnitaryPath pauliY t ≠ c • 1 :=
  eventually_hermitianUnitaryPath_nonscalar pauliY pauliY_nonscalar

example (t : ℝ) : hermitianUnitaryPath pauliY t *
    (hermitianUnitaryPath pauliY t)ᴴ = 1 :=
  hermitianUnitaryPath_mul_conjTranspose pauliY pauliY_hermitian t

example (s t : ℝ) : hermitianUnitaryPath pauliY (s + t) =
    hermitianUnitaryPath pauliY s * hermitianUnitaryPath pauliY t :=
  hermitianUnitaryPath_add pauliY s t

example (t : ℝ) : NormedSpace.exp
    (t • (Complex.I • (pauliY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliY.map (starRingEnd ℂ)))) =
    hermitianUnitaryPath pauliY t ⊗ₖ
      (hermitianUnitaryPath pauliY t).map (starRingEnd ℂ) :=
  exp_rowCommutator pauliY t

-- Empty matrices do not acquire a hidden nonempty-index premise.
example (t : ℝ) : hermitianUnitaryPath (0 : Matrix (Fin 0) (Fin 0) ℂ) t = 1 := by
  simp [hermitianUnitaryPath]

end ContinuousHermitianPathTest

/--
info: 'Matrix.hermitianUnitaryPath_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.hermitianUnitaryPath_zero

/--
info: 'Matrix.continuous_hermitianUnitaryPath' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.continuous_hermitianUnitaryPath

/--
info: 'Matrix.hermitianUnitaryPath_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.hermitianUnitaryPath_add

/--
info: 'Matrix.hermitianUnitaryPath_mul_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.hermitianUnitaryPath_mul_conjTranspose

/--
info: 'Matrix.hermitianUnitaryRepresentation' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.hermitianUnitaryRepresentation

/--
info: 'Matrix.eventually_hermitianUnitaryPath_nonscalar' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.eventually_hermitianUnitaryPath_nonscalar

/--
info: 'Matrix.exp_kronecker_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exp_kronecker_one

/--
info: 'Matrix.exp_one_kronecker' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exp_one_kronecker

/--
info: 'Matrix.exp_kronecker_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exp_kronecker_sum

/--
info: 'Matrix.exp_map_conjugate' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exp_map_conjugate

/--
info: 'Matrix.exp_rowCommutator' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exp_rowCommutator
