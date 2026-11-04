/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Schwarz.EntropicJensen

/-! Axiom and singular-boundary regressions for Wolf Equation (5.33). -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

/--
info: 'IsPositiveMap.entropic_jensen_subunital' depends on axioms:
  [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.entropic_jensen_subunital

/--
info: 'IsPositiveMap.entropic_jensen' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.entropic_jensen

-- Zero input for arbitrary rectangular positive unital maps.
example {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {T : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (hT : IsPositiveMap T) (hUnit : T 1 = 1) :
    T 0 * CFC.log (T 0) ≤ T ((0 : Matrix m m ℂ) * CFC.log 0) :=
  hT.entropic_jensen hUnit Matrix.PosSemidef.zero

-- Empty source and target indices introduce no nonemptiness assumption.
example {T : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ}
    (hT : IsPositiveMap T) (hSub : T 1 ≤ 1)
    {A : Matrix (Fin 0) (Fin 0) ℂ} (hA : A.PosSemidef) :
    T A * CFC.log (T A) ≤ T (A * CFC.log A) :=
  hT.entropic_jensen_subunital hSub hA

example {T : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ}
    (hT : IsPositiveMap T) (hUnit : T 1 = 1)
    {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.PosSemidef) :
    T A * CFC.log (T A) ≤ T (A * CFC.log A) :=
  hT.entropic_jensen hUnit hA

-- A concrete singular input: the rank-one diagonal projection in dimension two.
example {T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ}
    (hT : IsPositiveMap T) (hUnit : T 1 = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := diagonal (fun i => if i = 0 then 1 else 0)
    T A * CFC.log (T A) ≤ T (A * CFC.log A) := by
  dsimp only
  apply hT.entropic_jensen hUnit
  exact Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)

-- The rectangular zero map is positive and subunital.
example {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    let T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ := 0
    T A * CFC.log (T A) ≤ T (A * CFC.log A) := by
  dsimp only
  have hT : IsPositiveMap
      (0 : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ) := by
    intro B _
    exact Matrix.PosSemidef.zero
  exact hT.entropic_jensen_subunital Matrix.PosSemidef.one.nonneg hA
