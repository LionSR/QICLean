/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.LeadingEigenvector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the leading eigenvector of a near-optimal left state. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.IsHermitian.re_trace_mul_eq_sum_eigenvalues_mul,
    ``Matrix.PosSemidef.exists_eigenvector_of_re_trace_mul_le,
    ``Matrix.trace_gluing_mul_kronecker_one, ``Matrix.exists_leading_eigenvector_of_gluing]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
