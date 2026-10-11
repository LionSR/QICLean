/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InverseCompressionLowerPin
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the noncommuting inverse-compression comparison against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.mul_conjTranspose_le_smul_one_of_conjTranspose_mul_le,
      ``Matrix.PosDef.inv_smul_projection_le_of_compression_inv_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
