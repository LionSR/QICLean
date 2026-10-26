/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DensityMaxEigenvector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for a maximal density eigenvector. -/

open Matrix

run_cmd do
  let decl := ``PosSemidef.exists_unit_eigenvector_max_eigenvalue
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
