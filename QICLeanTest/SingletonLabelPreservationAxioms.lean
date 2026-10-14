/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.LabelPreservation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of one-site label preservation under replica transport. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``TensorPower.commute_labelProj_singleton_labelObservable,
    ``TensorPower.commute_labelProj_symProj_of_subset,
    ``TensorPower.ReplicaTransport.commute_labelProj_singleton_symBandMetric,
    ``TensorPower.ReplicaTransport.TransportData.commute_labelProj_singleton_input,
    ``TensorPower.ReplicaTransport.TransportData.labelProj_singleton_mulVec_filteredVector]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
