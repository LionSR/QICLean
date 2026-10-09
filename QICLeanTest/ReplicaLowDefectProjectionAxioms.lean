/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectProjection
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the actual low-defect projection declarations against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.replicaJointCopyPerm,
      ``TensorPower.permOp_replicaJointCopyPerm,
      ``Matrix.replicaLowDefectProjection,
      ``Matrix.isStarProjection_replicaLowDefectProjection,
      ``Matrix.replicaLowDefectProjection_mulVec_of_sector,
      ``Matrix.replicaLowDefectProjection_fixed_conditions,
      ``Matrix.replicaLowDefectProjection_gap_mass_ge,
      ``Matrix.replicaLowDefectProjection_compression_le_of_component_bounds] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
