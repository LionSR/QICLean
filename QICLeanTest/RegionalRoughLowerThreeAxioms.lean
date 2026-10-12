/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.RegionalRoughLowerThree
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for the fixed-weight rough lower comparison. -/

run_cmd do
  let decl := ``Matrix.exists_replicaMetric_symProj_bandProduct_rough_lower_norm_three
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
