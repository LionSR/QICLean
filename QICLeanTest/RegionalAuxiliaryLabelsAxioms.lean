/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalAuxiliaryLabels
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the two original auxiliary labels under the actual coordinate equivalence. -/

run_cmd do
  let decl := ``TensorPower.labelProj_globalReplicaCopiesEquiv_auxiliary
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
