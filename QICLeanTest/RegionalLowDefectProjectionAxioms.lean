/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectProjection
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the common original low-defect projection
under regional coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.addedSiteSpace,
      ``FiniteProduct.regionalPhysicalEquiv,
      ``TensorPower.replicaPhysicalCoordinateEquiv,
      ``TensorPower.regionalFiveFactorSpace,
      ``TensorPower.globalReplicaCopiesEquiv,
      ``TensorPower.regionalFiveFactorCopyEquiv,
      ``PermutationRepresentation.symProj_of_intertwine,
      ``Matrix.isStarProjection_conjTranspose_mul_mul_of_mul_range_eq,
      ``Matrix.replicaHamiltonian_submatrix_equiv,
      ``Matrix.replicaDefectCount_submatrix_equiv,
      ``TensorPower.symProj_replicaJointCopyPerm_reindex_physical,
      ``Matrix.replicaLowDefectProjection_reindex_physical,
      ``TensorPower.symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv,
      ``Matrix.globalReplicaLowDefectProjection,
      ``Matrix.globalReplicaLowDefectProjection_properties,
      ``Matrix.regionalFiveFactor_lowDefectProjection_eq_global] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
