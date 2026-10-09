/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaJointAuxiliaryExponential
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the joint auxiliary comparisons against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.commute_subgroup_labelObservables_of_subset_or_disjoint,
      ``Matrix.replicaGoodBadSplit,
      ``TensorPower.fiveFactorCopiesEquiv_auxiliary_permOp,
      ``TensorPower.fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep,
      ``TensorPower.copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression,
      ``TensorPower.copyPerm_groupedGood_auxiliaryPair_exp_compression,
      ``TensorPower.fiveFactor_groupedGood_auxiliaryPair_floor,
      ``TensorPower.fiveFactor_groupedGood_exp_le_without_auxiliary,
      ``Matrix.replicaExcitationComponent_exp_good_le_without_auxiliary] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
