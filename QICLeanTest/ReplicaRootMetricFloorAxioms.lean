/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Representation.ReplicaTransport.RootMetricFloor
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom checks for transport root floors and normalization bounds

The checks permit only propositional extensionality, classical choice and
quotient soundness in the transport root estimates.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.ReplicaTransport.exists_rootPath_scalar_floor,
      ``TensorPower.ReplicaTransport.exists_rootPath_log_filteredNormSq_bound] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
