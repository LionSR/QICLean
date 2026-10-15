/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityClipping
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for the clipped joint spectrum of commuting density matrices. -/

run_cmd do
  let decl := ``Matrix.PosSemidef.exists_unitary_diagonal_clipped_of_forall_density
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
