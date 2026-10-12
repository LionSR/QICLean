/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedTreeExpectation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the cutoff and inverse-power estimates for replica bands. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TensorPower.replicaBandRegions_subset_or_disjoint,
    ``TensorPower.exists_replicaMetric_cutoff_norm_bound,
    ``TensorPower.exists_replicaPinnedLeaf_expectation_le,
    ``Matrix.MeanTree.re_inner_eval_le_of_forall,
    ``Matrix.MeanTree.re_inner_rpow_eval_le_of_forall,
    ``Matrix.MeanTree.norm_inner_sq_le_rpow_mul_inverse_norm_sq,
    ``TensorPower.replicaPinnedTree_eval_eq_prod,
    ``TensorPower.exists_replicaPinnedTree_inverse_norm_bound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
