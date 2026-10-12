/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionSymmetry
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the Gram matrix, symmetry, and physical coordinates of tensor insertion. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``TensorPower.addedSiteConfigEquiv,
    ``TensorPower.addedSiteInsertion_conjTranspose_mul,
    ``TensorPower.isIsometry_addedSiteInsertion,
    ``TensorPower.permOp_copyPerm_mul_addedSiteInsertion,
    ``TensorPower.symProj_mul_addedSiteInsertion,
    ``TensorPower.addedSiteInsertion_mulVec_mem_symmetricSubspace,
    ``TensorPower.bellInsertionSiteEquiv,
    ``TensorPower.bellInsertionCopyEquiv,
    ``TensorPower.bellInsertionCopyEquiv_subsystemPerm_withPin,
    ``TensorPower.bellInsertionCopyEquiv_subsystemPerm_exterior,
    ``TensorPower.labelObservable_bellInsertionCopyEquiv_withPin,
    ``TensorPower.labelObservable_bellInsertionCopyEquiv_exterior,
    ``TensorPower.labelObservable_mul_bellInsertion_withPin,
    ``TensorPower.labelObservable_mul_bellInsertion_exterior,
    ``TensorPower.isIsometry_bellInsertion,
    ``TensorPower.permOp_copyPerm_mul_bellInsertion,
    ``TensorPower.symProj_mul_bellInsertion,
    ``TensorPower.labelObservable_mul_bellInsertion_auxiliary]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
