/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaBadCopyExponential
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for actual bad-copy exponential removal. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.replicaGoodBadSplit,
      ``PermutationRepresentation.labelEntropy_mul_symProj_of_eq_mul,
      ``TensorPower.commute_subsystemPerm_of_commute,
      ``TensorPower.commute_subgroup_labelObservable_symProj_of_subset,
      ``TensorPower.subgroup_signedLabelEntropy_symProj_nonneg,
      ``TensorPower.commute_grouped_labelObservables,
      ``TensorPower.commute_good_labelObservable_bad_symProj,
      ``TensorPower.re_dotProduct_exp_grouped_signedLabelEntropy_le,
      ``TensorPower.fiveFactorCopiesEquiv_simultaneous_permOp,
      ``Matrix.replicaGoodBadSplit_bad_image,
      ``Matrix.replicaExcitationComponent_mem_bad_invariantSubspace,
      ``Matrix.replicaExcitationComponent_exp_grouped_le_good] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
