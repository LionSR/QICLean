/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationIndividualMergeMoment
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for separate merge moments in the actual component. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.replicaGoodPairMarginal_exp_mergeDeficits_le,
      ``Matrix.replicaGoodPairMarginal_exp_sum_mergeDeficit_le,
      ``Matrix.replicaGoodConfigurationMarginal_exp_mergeDeficits_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
