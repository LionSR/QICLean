/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevSpectralProjector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the Chebyshev filter as a spectral projector. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``ContinuousLinearMap.aeval_map_apply_of_apply_eq_smul,
    ``Submodule.isSpectralProjector_aeval, ``Submodule.exists_isSpectralProjector_chebyshev]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
