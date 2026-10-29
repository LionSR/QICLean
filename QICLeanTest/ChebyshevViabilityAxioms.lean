/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevViability
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of Chebyshev improvement from a common polynomial family. -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.chebyshev_viability_of_polynomial_reduction,
    ``Matrix.chebyshev_viability_of_conjugated_polynomial_family,
    ``Matrix.chebyshev_viability_of_conjugated_polynomial_family_of_card_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
