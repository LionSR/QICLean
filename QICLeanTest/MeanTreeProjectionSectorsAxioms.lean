/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeProjectionSectors
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check mean trees on complementary projection ranges against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.posDef_smul_one_sub_add_smul_projection,
      ``Matrix.MeanTree.eval_smul_one_sub_add_smul_projection,
      ``Matrix.MeanTree.smul_one_sub_add_smul_projection_le_eval] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
