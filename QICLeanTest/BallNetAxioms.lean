/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BallNet
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of nets of the unit ball. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Metric.card_le_of_le_dist_of_subset_closedBall,
    ``Metric.packingNumber_le_of_subset_closedBall,
    ``Metric.exists_finset_net_of_subset_closedBall]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
