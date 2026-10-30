/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Semigroup.Basic
import QICLean.Channel.Semigroup.LindbladForm.TraceBridge
import QICLean.Channel.Peripheral.RecurrentInverse
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Regression checks for composition and evaluation in the matrix operator topology. -/

open scoped Matrix.Norms.Operator
open TNLean

-- The integral identity still covers arbitrary dimensions, including the zero space.
example {D : ℕ} (L : MatrixCLM (Fin D)) (t : ℝ) :
    intervalIntegral (fun s : ℝ => expSemigroupCLM L s) 0 t MeasureTheory.volume * L =
      L * intervalIntegral (fun s : ℝ => expSemigroupCLM L s) 0 t MeasureTheory.volume :=
  intervalIntegral_expSemigroupCLM_mul_generator_comm L t

example (L : MatrixCLM (Fin 0)) (t : ℝ) :
    expSemigroupCLM L t - 1 =
      intervalIntegral (fun s : ℝ => expSemigroupCLM L s) 0 t MeasureTheory.volume * L :=
  expSemigroupCLM_sub_one_eq_intervalIntegral_mul L t

example (L : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ)
    (hL : IsTraceAnnihilating L) (t : ℝ) :
    IsTracePreservingMap (expSemigroup L t) :=
  isTracePreservingMap_expSemigroup_of_isTraceAnnihilating L hL t

-- These checks also cover the evaluation map and the semigroup reconstruction proof.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``intervalIntegral_expSemigroupCLM_mul_generator_comm,
    ``expSemigroupCLM_sub_one_eq_intervalIntegral_mul,
    ``hasDerivAt_expSemigroup_apply,
    ``continuousDynSemigroup_eq_exp,
    ``isTracePreservingMap_expSemigroup_of_isTraceAnnihilating,
    ``isTraceAnnihilating_of_isTracePreservingMap_semigroup,
    ``IsPositiveMap.peripheralProjection_isSchwarzMap,
    ``IsPositiveMap.traceAdjointMap_peripheralProjection_isSchwarzMap,
    ``IsPositiveMap.exists_peripheralRestrictedInverse] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
