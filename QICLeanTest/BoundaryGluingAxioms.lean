/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.BoundaryGluing
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the gluing lemma of Landau, Vazirani and Vidick. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.partialTraceFirst, ``Matrix.conjTranspose_mulVec_gluing,
    ``Matrix.partialTraceRight_gluing,
    ``Matrix.partialTraceFirst_gluing, ``Matrix.rectangularTraceNorm_partialTraceFirst_gluing_sub,
    ``Matrix.norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm, ``Matrix.re_trace_gluing_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
