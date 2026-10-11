/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationExpectation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for actual good-copy densities and exponential expectations. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.replicaGoodBadSplit,
      ``TensorPower.badConfigurationTraceEquiv,
      ``Matrix.replicaGoodConfigurationMarginal_eq_grouped_partialTrace,
      ``Matrix.replicaExcitationComponent_exp_good_eq_trace_goodConfigurationMarginal,
      ``Matrix.replicaExcitationComponent_exp_good_without_auxiliary_eq_trace] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
