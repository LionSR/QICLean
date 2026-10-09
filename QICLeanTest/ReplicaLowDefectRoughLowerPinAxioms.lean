/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectRoughLowerPin
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the actual rough lower bound and its coordinate identities against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.isStarProjection_conjTranspose_mul_mul_of_mul_range_eq,
      ``PermutationRepresentation.symProj_of_intertwine,
      ``Matrix.PosDef.lower_pin_of_reindexed_inverse_compression,
      ``TensorPower.symProj_replicaJointCopyPerm_submatrix_fiveFactorCopiesEquiv,
      ``TensorPower.isStarProjection_compressed_replicaLowDefectProjection,
      ``Matrix.exists_replicaLowDefectProjection_rough_lower_pin] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
