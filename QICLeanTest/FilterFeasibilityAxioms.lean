/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterFeasibility

/-! Require every bridge declaration to depend only on the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.IsFeasibleFilter.posSemidef,
      ``Entropy.IsFeasibleFilter.trace_cfc_rpow,
      ``Entropy.isFeasibleFilter_zero_iff,
      ``Entropy.isFeasibleFilter_zero_iff_eigenvalues,
      ``Entropy.IsFeasibleFilter.reindex,
      ``Entropy.isFeasibleFilter_reindex_iff] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
