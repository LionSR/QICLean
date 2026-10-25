/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of closeness and viability of subspaces. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.IsCloseTo, ``Submodule.isCloseTo_iff,
    ``Submodule.IsCloseTo.exists_mem_starProjection_eq,
    ``Submodule.IsCloseTo.trans]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
