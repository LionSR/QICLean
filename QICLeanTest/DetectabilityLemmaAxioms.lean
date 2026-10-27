/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DetectabilityLemma
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the detectability lemma and its converse. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``ContinuousLinearMap.complementProd,
    ``ContinuousLinearMap.norm_apply_complementProd_le,
    ``ContinuousLinearMap.re_inner_sum_complementProd_le,
    ``ContinuousLinearMap.norm_sq_complementProd_le,
    ``ContinuousLinearMap.isStarProjection_complementProd,
    ``ContinuousLinearMap.norm_sq_sub_norm_sq_complementProd_le,
    ``IsStarProjection.one_sub_three_mul_le_norm_sq_mul_apply,
    ``ContinuousLinearMap.one_sub_three_mul_le_norm_sq_complementProd_mul]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
