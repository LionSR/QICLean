/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.CommutatorSeries
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom guards for the norm-convergent Gaussian commutator expansion. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``GaussianFilter.gaussianIntertwiner_eq_exp_commutator,
      ``GaussianFilter.hasSum_gaussianIntertwiner_commutator] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
