/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.TrimmedWitness
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the trimmed low-energy witness. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.ofLp_rightApply, ``Matrix.leftApply_smul, ``Matrix.leftApply_rightApply,
    ``Matrix.schmidtRank_leftApply_le_rank,
    ``Matrix.IsTrimmingProjection.leftApply_leftApply_of_leftApply_eq,
    ``Matrix.IsTrimmingProjection.exists_trimmed_witness]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
