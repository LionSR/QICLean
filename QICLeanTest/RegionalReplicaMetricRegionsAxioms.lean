/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalReplicaMetricRegions
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the actual left, far and middle regions and their induced partition. -/

run_cmd do
  let names := #[``TensorPower.regionalOriginalRegion_metric_regions,
    ``TensorPower.regionalOriginalRegion_metric_partition]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
