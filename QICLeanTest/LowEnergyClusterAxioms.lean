/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyCluster
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Allowed-axiom audit for dimension comparison and the low-energy cluster theorem. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.IsCloseTo.finrank_le,
    ``Submodule.eq_and_isCloseTo_of_le,
    ``Submodule.low_spectral_cluster_of_restricted_residuals]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
