/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedSharpTree
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exact-name standard-axiom checks for supplied-sector multi-band sharp bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TensorPower.selectedBellPost,
    ``TensorPower.exists_selectedBellPost_sharp_tree_bounds]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
