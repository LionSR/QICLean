/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationSingletonMoment
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the actual three physical singleton moments. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.physicalSingletonEquiv,
      ``TensorPower.fiveFactorCopies_labelObservable_singleton,
      ``TensorPower.fiveFactorCopies_exp_labelEntropy_singleton,
      ``Matrix.trace_replicaGoodConfigurationMarginal_exp_singleton_labelEntropy] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
