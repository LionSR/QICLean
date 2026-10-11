/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaExcitationCompression
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the excitation-component compression theorems against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.PosSemidef.re_dotProduct_sum_mulVec_le_card_sum,
      ``Matrix.re_dotProduct_replicaDefectCutoff_le_of_component_bounds,
      ``Matrix.compression_le_of_replicaExcitationComponent_bounds] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
