/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceMulBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the trace pairings with positive semidefinite matrices. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.norm_star_dotProduct_mulVec_le,
    ``Matrix.PosSemidef.norm_trace_mul_le,
    ``Matrix.l2_opNorm_one_kronecker_le,
    ``Matrix.PosSemidef.norm_trace_mul_mul_le,
    ``Matrix.PosSemidef.re_trace_mul_mul_self_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
