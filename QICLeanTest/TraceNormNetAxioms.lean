/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceNormNet
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the trace-norm net. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.norm_apply_le_l2_opNorm, ``Matrix.norm_apply_le_rectangularTraceNorm,
    ``Matrix.rectangularTraceNorm_single_one_le, ``Matrix.rectangularTraceNorm_le_sum_norm_apply,
    ``Matrix.exists_finset_rectangularTraceNorm_net]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
