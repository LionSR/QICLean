/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceRandomSampling
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of random sampling of a viable subspace. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.starProjection_map_linearIsometry, ``Submodule.isCloseTo_of_net,
    ``Submodule.tensorProd_mono_left, ``Submodule.randomSubspace,
    ``Submodule.finrank_randomSubspace,
    ``Submodule.unitaryHaar_norm_sq_starProjection_randomSubspace_le,
    ``Submodule.unitaryHaar_not_isViable_randomSubspace_le,
    ``Submodule.exists_isViable_randomSubspace]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
