/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Representation.ReplicaTransport.SymmetricMetricFloor
import QICLean.Analysis.Transport.MetricFloor
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for product metric floors and filtered-norm bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.ReplicaTransport.exists_meanTree_symBandMetric_prod_floor,
      ``Matrix.PosDef.rpow_le_smul_one_of_scalar_floor,
      ``Matrix.Transport.filteredNormSq_le_of_scalar_floor,
      ``Matrix.Transport.log_filteredNormSq_le_of_rpow_floor] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
