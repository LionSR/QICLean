/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.PatchNormalizedFirstVariation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for first-order inequalities at normalized patch outputs. -/

run_cmd do
  let decl := ``Entropy.re_trace_variation_le_of_isPatchMinimizer
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
