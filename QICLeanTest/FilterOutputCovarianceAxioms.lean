/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterOutputCovariance

/-! Require every ordered-output and relabelling theorem to use only standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.foldl_toEuclideanCLM_eq_reverse_prod,
      ``Entropy.foldl_localLift_eq_liftProd_chainList,
      ``Entropy.localLift_relabel,
      ``Entropy.liftProd_chainList_relabel,
      ``Entropy.relabelVector_liftProd_chainList,
      ``Entropy.relabelVector_normalized_liftProd_chainList,
      ``Entropy.forall_norm_liftProd_chainList_le_relabel_iff] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
