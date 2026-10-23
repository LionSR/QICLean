/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MarginalRank
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit of the rank bound from marginal supports. -/

run_cmd do
  let decl := ``Matrix.PosSemidef.rank_le_rank_partialTraceRight_mul_rank_partialTraceLeft
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
