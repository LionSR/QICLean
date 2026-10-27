/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalMovement.DoubleCurve
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Regression checks for proof-local finite-coordinate choices in the movement curve. -/

-- Row and output indices need only finiteness, not chosen enumerations or equality tests.
example {ι κ ζ : Type*} [Finite ι] [Fintype κ] [Finite ζ] :
    Differentiable ℂ (fun D : Matrix ι κ ℂ × Matrix κ ζ ℂ => D.1 * D.2) :=
  ConditionalMovement.LocalMove.matrixMul_differentiable

-- Empty outer dimensions are still admitted, with no nonemptiness premise.
example {κ : Type*} [Fintype κ] :
    Differentiable ℂ
      (fun D : Matrix (Fin 0) κ ℂ × Matrix κ (Fin 0) ℂ => D.1 * D.2) :=
  ConditionalMovement.LocalMove.matrixMul_differentiable

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``ConditionalMovement.LocalMove.matrixMul_differentiable,
    ``ConditionalMovement.LocalMove.doubleCurve_differentiable,
    ``ConditionalMovement.LocalMove.doubleCurve_bounded,
    ``ConditionalMovement.LocalMove.one_copy_interpolation_fullrank] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
