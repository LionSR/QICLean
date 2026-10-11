/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.IidSurprisalMomentExponential
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the tensor-power exponential identities against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.IsHermitian.exp_smul_sub_smul_one_eq_cfc,
      ``Matrix.PosSemidef.re_trace_finKronecker_exp_centered_surprisal] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
