/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectSharpCompression
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the uniform sharp bound and its actual low-defect compression. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Matrix.exists_replicaExcitationComponent_inverse_sharp_uniform_le,
    ``Matrix.exists_replicaLowDefectProjection_inverse_sharp_compression_le]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
