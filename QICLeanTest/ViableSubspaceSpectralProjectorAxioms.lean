/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSpectralProjector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of error reduction of a viable subspace by a spectral projector. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.tmul_mem_tensorProd, ``Submodule.tensorProd_le_iff,
    ``Submodule.finrank_iSup_le_sum, ``Submodule.IsSpectralProjector,
    ``Submodule.IsSpectralProjector.contract, ``Submodule.IsViable.spectralProjector]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Submodule.IsViable.map_of_tensor_decomposition]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
