/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OverlapEnergy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the auxiliary overlap-to-energy estimates. -/

run_cmd do
  let names := #[``LinearMap.IsSymmetric.re_inner_sub_eigenvalue_le_of_norm_sub_le,
    ``LinearMap.IsSymmetric.re_inner_sub_eigenvalue_le_of_overlap]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {name}: {axioms}"
    Lean.logInfo m!"{name}: {axioms}"
