/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionRegisterCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit changes of local coordinates and of the inserted Bell register. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``TensorPower.subsystemPerm_piCongrRight,
    ``TensorPower.bellInsertion_submatrix_C_equiv]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
