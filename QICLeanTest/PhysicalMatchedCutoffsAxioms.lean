/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedPhysicalMatchedCutoffs
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit subsystem label dimensions and the matched physical cutoff. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``PermutationRepresentation.dim_le_card_of_labelProj_ne_zero,
    ``TensorPower.dim_le_pow_card_of_subsystem_labelProj_ne_zero,
    ``TensorPower.labelCutoff_subsystemPerm_mul_of_nested,
    ``TensorPower.toEuclideanLin_labelCutoff_of_matched,
    ``FiniteProduct.exteriorRegion_symmDiff,
    ``FiniteProduct.card_configuration_exteriorRegion_symmDiff,
    ``FiniteProduct.toEuclideanLin_compressedPhysicalCutoff_of_matched]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
