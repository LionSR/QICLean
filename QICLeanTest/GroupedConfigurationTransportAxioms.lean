/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.GroupedConfigurationTransport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for observables in grouped copy coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.groupedConfigurationEquiv,
      ``TensorPower.groupedConfigurationEquiv_subsystemPerm,
      ``TensorPower.groupedConfigurationEquiv_labelObservable,
      ``TensorPower.groupedConfigurationEquiv_exp_sum_labelEntropy] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
