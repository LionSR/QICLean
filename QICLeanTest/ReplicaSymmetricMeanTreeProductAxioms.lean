/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSymmetricMeanTreeProduct
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for common-tree products of actual replica bands. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.commute_subgroup_labelObservables_of_subset_or_disjoint,
      ``TensorPower.commute_labelObservables_subsystemPerm_of_laminar,
      ``TensorPower.posDef_replicaPinnedLeaf,
      ``TensorPower.posDef_replicaPinnedFactor,
      ``TensorPower.replicaPinnedBands_posDef_commute,
      ``TensorPower.replicaMetric_factors_symProj,
      ``Matrix.PosDef.compression_of_projection_intertwine,
      ``Matrix.commute_of_isometric_intertwine,
      ``TensorPower.replicaMetric_symProj_compressions_posDef_commute,
      ``TensorPower.replicaMetric_symProj_meanTree_roots_commute,
      ``TensorPower.replicaMetric_symProj_meanTree_eq_product] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
