/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPrevectorSharpUpper
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exact-name standard-axiom checks for the supplied-sequence sharp upper rate. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Real.neg_log_div_le_of_sharp_bell_bound,
    ``TensorPower.eventually_suppliedSchmidtBell_sharp_upper,
    ``FiniteProduct.eventually_suppliedReplicaPrevector_sharp_upper]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
