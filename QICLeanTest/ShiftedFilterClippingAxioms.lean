/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedFilterClipping
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for inverse-power filters with clipped eigenvalues. -/

run_cmd do
  let decl := ``Matrix.exists_clipped_rpow_add_smul_one_of_diagonal_max
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
