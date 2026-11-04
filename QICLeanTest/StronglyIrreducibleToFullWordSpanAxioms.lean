/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom guard for the discrete quantum-Wielandt implication (issue #525). -/

run_cmd do
  let decl := ``Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
