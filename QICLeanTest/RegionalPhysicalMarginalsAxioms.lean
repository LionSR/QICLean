/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalPhysicalMarginals
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the original regional marginals and their spectral statistics. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``FiniteProduct.regionalPhysicalRegion,
    ``Matrix.regional_physicalSingletonDensity_eq_reducedPure,
    ``Matrix.regional_physicalSingleton_spectral_statistics]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
