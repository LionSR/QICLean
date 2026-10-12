/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellSitePin
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the five exterior-coordinate Bell declarations. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``FiniteProduct.schmidtBellSiteEquiv,
    ``FiniteProduct.selectedBellProjection_schmidtBellSiteEquiv,
    ``FiniteProduct.labelProj_schmidtBellSiteEquiv,
    ``FiniteProduct.schmidtBellSiteEquiv_post,
    ``FiniteProduct.selectedBellProjection_replicaPrevector_site]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
