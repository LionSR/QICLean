/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyCluster
import QICLean.Analysis.SeparatedQuadraticForms
import QICLean.Analysis.SpectralExponentialWeights
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation audit of the actual public truncation results. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.PosSemidef.nonneg_of_normalized_eigenvector,
    ``Matrix.groundEnergy_eq_of_normalized_eigenvectors,
    ``Matrix.mulVec_eq_smul_of_order_sandwich,
    ``Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero,
    ``Matrix.centered_partially_clipped_sum_norm_le_budget,
    ``Matrix.commute_centered_partially_clipped_sum,
    ``Matrix.spectralProjectionGE_le_centered_partially_clipped_sum,
    ``Matrix.groundEnergy_bounds_of_positive_boundary_and_zero_test,
    ``Matrix.IsHermitian.norm_exp_mul_sub_const_mul_lowProjection_le_one,
    ``mul_inverse_weight_mul_eq_of_right_support,
    ``Matrix.IsHermitian.regionalWeight_relations,
    ``WeightedProjection.forcing_identity,
    ``Matrix.norm_projection_conjugated_mul_projection_le,
    ``Matrix.norm_weighted_projection_forcing_le,
    ``ContinuousLinearMap.exists_restricted_weighted_sylvester,
    ``ContinuousLinearMap.exists_restrict_range_quadratic_lower,
    ``OrthonormalBasis.re_inner_apply_eq_sum_of_eigen,
    ``Submodule.re_inner_apply_le_of_mem_spectralSpanLE,
    ``Submodule.commute_starProjection_spectralSpanLE,
    ``ContinuousLinearMap.norm_le_of_subtypeL_comp_eq_domRestrict,
    ``ContinuousLinearMap.mul_norm_le_norm_sylvester_of_quadratic_bounds,
    ``ContinuousLinearMap.norm_le_div_of_sylvester_perturbation,
    ``Matrix.toEuclideanCLM_le_of_le,
    ``Real.sub_mul_exp_weight_le,
    ``Real.posPart_sub_mul_exp_weight_le,
    ``Matrix.IsHermitian.norm_excess_domRestrict_le_actual_weighted_map,
    ``Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms,
    ``Matrix.norm_centered_clipping_discrepancy_domRestrict_le_sum,
    ``Submodule.low_spectral_cluster_of_restricted_residuals]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
