/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationMergeMoment
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for actual good-copy merge observables and moments. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.fiveFactorPairMiddle_labelObservable,
      ``TensorPower.fiveFactorPairMiddle_mergeDeficits,
      ``TensorPower.fiveFactorPairMiddle_exp_sum_mergeDeficit,
      ``Matrix.trace_replicaGoodConfigurationMarginal_exp_sum_mergeDeficit,
      ``Matrix.replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
