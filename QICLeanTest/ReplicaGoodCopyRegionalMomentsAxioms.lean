/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationRegionalMoment
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for regional observables of the actual good-copy density. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.trace_replicaGoodConfigurationMarginal_regional_mul,
      ``Matrix.trace_replicaGoodConfigurationMarginal_regional_exp_labelEntropy] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
