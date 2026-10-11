/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaGroupedInverse
import QICLean.Representation.ReplicaDisjointMetricPositivity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the disjoint and grouped replica metric statements against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.posDef_replicaMetric_disjoint_inv_mul_inv_mul,
      ``TensorPower.posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq,
      ``TensorPower.exp_neg_whole_labelEntropy_le_exp_grouped,
      ``TensorPower.exists_replicaMetric_inv_square_le_grouped_exp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
