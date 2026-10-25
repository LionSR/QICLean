/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceHolderMulti
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the multi-factor Hölder inequality for traces with positive
definite factors and of its imaginary-time specialization. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.norm_trace_list_prod_mul_exp_smul_le,
    ``Matrix.IsHermitian.norm_trace_list_prod_mul_exp_neg_smul_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
