/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.HaarProjection
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the projection onto a Haar-random coordinate subspace. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``QICLean.HaarProjection.weightCone,
    ``QICLean.HaarProjection.isClosed_weightCone,
    ``QICLean.HaarProjection.smul_mem_weightCone_iff,
    ``QICLean.HaarProjection.stdGaussian_singleton_zero,
    ``QICLean.HaarProjection.sampleEquiv, ``QICLean.HaarProjection.coordinate_eq,
    ``QICLean.HaarProjection.law_map_sampleEquiv,
    ``QICLean.HaarProjection.unitaryAction, ``QICLean.HaarProjection.ofLp_unitaryAction,
    ``QICLean.HaarProjection.starAction, ``QICLean.HaarProjection.ofLp_starAction,
    ``QICLean.HaarProjection.exists_unitary_mulVec_eq,
    ``QICLean.HaarProjection.unitaryHaar_weightCone_eq_of_ne_zero,
    ``QICLean.HaarProjection.unitaryHaar_weightCone_eq_stdGaussian,
    ``QICLean.HaarProjection.unitaryHaar_sum_norm_sq_le,
    ``QICLean.HaarProjection.coordinateSubspace,
    ``QICLean.HaarProjection.starProjection_coordinateSubspace,
    ``QICLean.HaarProjection.norm_sq_starProjection_coordinateSubspace,
    ``QICLean.HaarProjection.norm_sq_starProjection_map_coordinateSubspace,
    ``QICLean.HaarProjection.unitaryHaar_norm_sq_starProjection_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
