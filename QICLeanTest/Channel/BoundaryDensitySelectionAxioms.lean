/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.BoundaryDensitySelection
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for a minimizing density and its leading unit eigenvector. -/

run_cmd do
  let decl := ``Matrix.exists_boundary_density_minimizer_max_eigenvector
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
