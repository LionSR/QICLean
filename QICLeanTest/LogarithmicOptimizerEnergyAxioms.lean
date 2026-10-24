/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterChainEnergy

/-! Logical-dependency checks for stationary and actual-maximizer energy bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.re_inner_sub_le_of_chain_logarithmic,
      ``Entropy.re_inner_sub_le_of_max_logarithmic,
      ``Entropy.re_inner_sub_le_of_chain_sharp,
      ``Entropy.re_inner_sub_le_of_max,
      ``Entropy.re_inner_sub_le_of_max_sharp,
      ``Entropy.abs_re_inner_sub_le_of_max_sharp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
