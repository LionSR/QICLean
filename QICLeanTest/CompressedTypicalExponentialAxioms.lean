/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.CompressedTypicalExponential
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for the compressed-state regional exponential identity. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TensorPower.re_inner_exp_labelEntropy_compressedTypicalSiteState_prod
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
