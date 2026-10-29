/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebTraceExponential
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of Lieb's concavity theorem for the trace exponential. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``re_trace_sub_re_trace_le_quantumRelativeEntropy,
    ``re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le,
    ``re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_exp_add_log,
    ``isGreatest_re_trace_exp_add_log,
    ``concaveOn_re_trace_exp_add_log]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
