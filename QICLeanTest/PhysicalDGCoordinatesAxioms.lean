/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevViability
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.MatrixTensorCoordinates
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.LowEnergyCluster
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for the public spectral-coordinate and viability results. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.IsHermitian.original_basis_centered_gap_data,
    ``Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum,
    ``Matrix.exists_canonical_isometric_spectral_data,
    ``Matrix.chebyshev_viability_of_actual_cluster_polynomial_family,
    ``Matrix.IsHermitian.two_le_local_dimension_of_two_spectral_values,
    ``Submodule.iSup_map_basis_matrixUnits_eq_top,
    ``Submodule.isViable_ne_bot_of_target_ne_bot,
    ``Submodule.exists_clm_family_extension_of_card_le,
    ``Submodule.low_spectral_cluster_of_scaled_restricted_residuals,
    ``Matrix.IsHermitian.spectralSpanLE_ne_bot_of_mem_spectrum]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
