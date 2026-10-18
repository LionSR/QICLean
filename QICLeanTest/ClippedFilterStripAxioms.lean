/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterEnergy

/-! Logical-dependency checks for clipped modular strip and physical conjugation bounds. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.norm_modularExpectation_kronecker_le,
      ``Entropy.abs_re_modularExpectation_sub_le,
      ``Entropy.norm_modularExpectation_kronecker_le_of_log_clipping,
      ``Entropy.abs_re_inner_sub_inner_conj_le_logarithmic,
      ``Entropy.abs_re_inner_sub_conj_le_of_common_basis_logarithmic,
      ``Entropy.abs_re_inner_sub_conj_le_of_common_basis_sharp,
      ``Entropy.cutBasisChange_conj_sum_kronecker] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
