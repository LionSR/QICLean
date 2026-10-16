/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterZeroFloorEnergy

/-! Check the maximizing family and both energy statements against the standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.exists_max_feasible_chain_mem_of_pos_floor,
      ``Entropy.norm_liftProd_pos_of_zero_floor_max,
      ``Entropy.exists_max_feasible_chain_zero_floor_energy,
      ``Entropy.exists_max_feasible_chain_zero_floor_normalized_energy,
      ``Entropy.re_inner_sub_le_of_max_sharp,
      ``Entropy.abs_re_inner_sub_le_of_max_sharp,
      ``Entropy.exists_max_feasible_chain_zero_floor_abs_energy_sharp,
      ``Entropy.exists_max_feasible_chain_zero_floor_normalized_abs_energy_sharp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

