/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPinnedTreeAction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of Bell restriction for the original replica metrics. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TensorPower.commute_labelObservable_symProj,
    ``TensorPower.labelObservable_mul_bellInsertion_symProj_far,
    ``TensorPower.replicaMetric_factor_mul_bellInsertion_symProj,
    ``TensorPower.posDef_bellMetric_factors,
    ``TensorPower.isStarProjection_bellInsertion_symProj,
    ``TensorPower.commute_labelObservable_bellPin,
    ``TensorPower.replicaMetric_factors_bellPin,
    ``TensorPower.replicaMetric_meanTree_bellPin]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
