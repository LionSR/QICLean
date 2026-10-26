/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.BoundaryDensityMinimizer
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted-axiom checks for closed trace-norm sublevels and a minimizing left state. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.isClosed_setOf_rectangularTraceNorm_le,
    ``Matrix.exists_boundary_density_minimizer] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
