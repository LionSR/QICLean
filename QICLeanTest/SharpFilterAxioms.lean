/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterChainEnergy

/-! Check sharp endpoints and preserved coarse counterparts against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.cosh_mul_sub_one_le_sq_mul,
      ``Entropy.sqrt_mul_cosh_sub_one_le_sharp, ``Entropy.card_innerConfig,
      ``Entropy.IsSupportedOn.hasProductDecomposition_inner,
      ``Entropy.IsSupportedOn.hasProductDecomposition,
      ``Entropy.abs_re_inner_sub_inner_conj_le_sharp,
      ``Entropy.abs_re_inner_sub_inner_conj_le,
      ``Entropy.abs_re_inner_sub_conj_le_of_common_basis_sharp,
      ``Entropy.abs_re_inner_sub_conj_le_of_common_basis,
      ``Entropy.abs_re_inner_sub_conj_localLift_le_sharp,
      ``Entropy.abs_re_inner_sub_conj_localLift_le,
      ``Entropy.abs_re_inner_sub_chain_conj_le_sharp,
      ``Entropy.abs_re_inner_sub_chain_conj_le,
      ``Entropy.re_inner_sub_le_of_chain_sharp,
      ``Entropy.re_inner_sub_le_of_chain] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    Lean.logInfo m!"{decl}: {axioms}"
