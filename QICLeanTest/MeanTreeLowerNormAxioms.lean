/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeExponentialLowerNorm
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the two lower norm comparisons against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Matrix.MeanTree.mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound,
      ``Matrix.MeanTree.explicit_lower_norm_of_exponential_projection_lower_bound] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
