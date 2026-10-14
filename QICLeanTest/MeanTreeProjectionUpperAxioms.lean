/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeProjectionUpper
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exact-name standard-axiom checks for supplied-sector upper bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.PosSemidef.re_dotProduct_projection_mulVec_le,
    ``Matrix.MeanTree.re_inner_log_eval_le_of_projection,
    ``Matrix.MeanTree.mass_rpow_mul_exp_le_norm_rpow_neg_eval_projection_sq]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
