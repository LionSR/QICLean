/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TensorPowerPartialTrace
import QICLean.Analysis.ReplicaGoodConfigurationPairMarginal
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for regrouped tensor products and actual good-copy marginals. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.copiesProductEquiv,
      ``Matrix.partialTraceRight_finKronecker_reindex,
      ``TensorPower.fiveFactorPairMiddleEquiv,
      ``Matrix.posSemidef_replicaGoodConfigurationMarginal,
      ``Matrix.partialTraceRight_replicaGoodConfigurationMarginal_pairMiddle,
      ``Matrix.trace_replicaGoodConfigurationMarginal,
      ``Matrix.trace_replicaGoodConfigurationMarginal_pairMiddle_mul] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
