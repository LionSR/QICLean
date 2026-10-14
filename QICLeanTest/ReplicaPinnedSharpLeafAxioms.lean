/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedSharpLeaf
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exact-name standard-axiom checks for the same-selection sharp leaf estimate. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``TensorPower.re_trace_mul_exp_pinnedLabels_le,
    ``TensorPower.re_inner_exp_labelEntropy_bellInsertion,
    ``TensorPower.exists_log_re_inner_replicaPinnedFactor_post_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
