/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcLogListProduct
import QICLean.Analysis.MeanTreeLogFloorExp
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check logarithmic product and floor estimates against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.cfc_log_listProd_ofFn,
      ``Real.sub_log_two_le_log_add_half_exp,
      ``Real.log_add_half_exp_sub_log_le,
      ``Matrix.MeanTree.weighted_log_add_half_exp_bounds] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
