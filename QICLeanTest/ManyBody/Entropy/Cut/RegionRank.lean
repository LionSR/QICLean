/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.Cut.RegionRank
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Empty-factor specialization and axiom audits for regional rank inequalities. -/

open Matrix

example {R : Type*} [Fintype R] (ψ : Empty × R → ℂ) :
    (partialTraceRight (vecMulVec ψ (star ψ))).rank =
      (partialTraceLeft (vecMulVec ψ (star ψ))).rank :=
  rank_partialTraceRight_vecMulVec_eq_rank_partialTraceLeft ψ

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.rank_partialTraceRight_vecMulVec_eq_rank_partialTraceLeft,
    ``ManyBody.rank_regionState_compl, ``ManyBody.rank_regionMatrix_union_le,
    ``Entropy.rank_regionState_union_le, ``Entropy.rank_regionState_sdiff_le]
  for decl in decls do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
