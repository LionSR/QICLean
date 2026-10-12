/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Representation.ReplicaMeanIdentityExtension
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for identity extension of the same replica mean. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TensorPower.siteOp_kronecker_one,
      ``TensorPower.replicaMean_kronecker_one,
      ``TensorPower.siteOp_eq_finKronecker] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
