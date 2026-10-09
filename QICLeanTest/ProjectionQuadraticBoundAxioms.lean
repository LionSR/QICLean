/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectionQuadraticBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check quadratic-form comparisons against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.re_dotProduct_mulVec_le_of_le,
      ``Matrix.IsHermitian.re_dotProduct_mulVec_le_of_compression_le,
      ``Matrix.star_dotProduct_submatrix_equiv] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
