/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the bootstrapping step for viable subspaces. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.IsCloseTo.of_le, ``Submodule.bootstrapFailure,
    ``Submodule.isViable_top, ``Submodule.exists_isViable_finrank_le_half,
    ``Submodule.exists_isViable_finrank_lt_of_bootstrap]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
