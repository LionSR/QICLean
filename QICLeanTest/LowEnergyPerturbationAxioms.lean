/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyPerturbation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the closeness of low-energy subspaces under a perturbation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.spectralSpanLE, ``Submodule.mem_spectralSpanLE_iff,
    ``Submodule.norm_sq_repr_symm, ``Submodule.repr_apply_of_eigen,
    ``Submodule.starProjection_orthogonal_spectralSpanLE,
    ``Submodule.norm_sq_starProjection_orthogonal_spectralSpanLE,
    ``Submodule.mul_norm_starProjection_orthogonal_le,
    ``Submodule.mul_norm_starProjection_orthogonal_le_of_window,
    ``Submodule.isCloseTo_spectralSpanLE_of_perturbation]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
