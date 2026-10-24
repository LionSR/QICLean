/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceExpAlternatingSum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the bound on alternating sums of shifted exponentials. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.norm_trace_mul_sum_powerset_exp_le,
    ``Matrix.norm_trace_mul_sum_powerset_exp_le_pow,
    ``Matrix.norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le,
    ``Matrix.norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le_pow,
    ``Matrix.norm_trace_list_prod_mul_sum_powerset_exp_le,
    ``Matrix.norm_trace_list_prod_mul_sum_powerset_exp_le_pow]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
