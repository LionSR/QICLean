/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixTensorCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of continuous matrix actions in tensor coordinates. -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.toEuclideanCLM_kronecker_intertwining,
    ``Matrix.toEuclideanCLM_submatrix_intertwining,
    ``Matrix.toEuclideanCLM_reindexed_kronecker_sum_intertwining,
    ``TensorProduct.intertwining_sum_mapL_commIsometry]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
