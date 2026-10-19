/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterChainEnergy

/-! Logical-dependency checks for supported and nested logarithmic conjugation bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.abs_re_inner_sub_chain_conj_le_sharp,
      ``Entropy.abs_re_inner_sub_conj_localLift_le_logarithmic,
      ``Entropy.abs_re_inner_sub_chain_conj_le_logarithmic] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
