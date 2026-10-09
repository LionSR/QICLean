/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.NormalizedInversePowerLogBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check normalized inverse-power logarithmic bounds against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.PosDef.mul_re_inner_cfc_log_le_neg_log_of_scaled_power_norm_le,
      ``Matrix.PosDef.mul_re_inner_cfc_log_normalized_inverse_le_neg_log_norm_sq] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
