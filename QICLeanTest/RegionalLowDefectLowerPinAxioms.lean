/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectLowerPin
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the original regional rough lower bound. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``FiniteProduct.norm_regionalPhysicalVector,
      ``Matrix.exists_globalReplicaLowDefectProjection_rough_lower_pin] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
