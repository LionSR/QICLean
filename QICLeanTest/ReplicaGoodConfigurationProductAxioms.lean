/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationProduct
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the good-copy product and its existing density consequences. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.goodAuxiliarySplit,
      ``Matrix.replicaGoodConfigurationMarginal_eq,
      ``Matrix.partialTraceRightAlong_kronecker,
      ``Matrix.partialTraceRight_replicaExcitationComponent_goodFin_density,
      ``Matrix.replicaGoodConfigurationMarginal_product,
      ``Matrix.partialTraceRight_replicaGoodConfigurationMarginal_physical,
      ``Matrix.trace_replicaGoodConfigurationMarginal_physical_mul,
      ``Matrix.symProj_mul_replicaGoodConfigurationMarginal,
      ``Matrix.replicaGoodRegionalAuxiliaryMarginal_eq] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
