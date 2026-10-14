/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SelectedBellPostInverseTransport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exact-name standard-axiom checks for literal same-sector Bell transport. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TensorPower.labelProj_mul_bellInsertion_auxiliary,
    ``TensorPower.norm_labelProj_bellInsertion_auxiliary,
    ``TensorPower.norm_sq_labelProj_selectedBellPost_eq,
    ``TensorPower.norm_sq_labelProj_selectedBellPost_prod,
    ``TensorPower.selectedBellPost_eq_pullback,
    ``TensorPower.symProj_labelProj_selectedBellPost,
    ``TensorPower.bellPin_schmidtBellPrevector_eq_selectedBellPost,
    ``TensorPower.selectedBellPost_inverse_norm_le_physical]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
