/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalReplicaMetric
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the original replica metric under regional grouping. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.regionalFactorIndex,
      ``TensorPower.regionalOriginalRegion,
      ``TensorPower.regionalFiveFactorCopyEquiv_subsystemPerm,
      ``TensorPower.groupAlgebraRep_submatrix_regionalFiveFactorCopyEquiv,
      ``TensorPower.labelObservable_submatrix_regionalFiveFactorCopyEquiv,
      ``TensorPower.replicaDim_regionalFiveFactorSpace,
      ``TensorPower.replicaLabelWeight_regionalFiveFactorSpace,
      ``TensorPower.replicaMetric_submatrix_regionalFiveFactorCopyEquiv,
      ``TensorPower.replicaMetric_inv_mul_inv_mul_sq_submatrix_regionalFiveFactorCopyEquiv] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
