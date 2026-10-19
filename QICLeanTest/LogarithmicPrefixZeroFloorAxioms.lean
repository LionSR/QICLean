/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterZeroFloor

/-! Logical-dependency checks for prefix iteration and its uniform floor-zero limit. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.sqrt_mul_chainOptimum_succ_le,
      ``Entropy.pow_sqrt_mul_chainOptimum_le,
      ``Entropy.pow_sqrt_mul_norm_le_of_zero_floor,
      ``Entropy.sqrt_mul_chainOptimum_succ_le_logarithmic,
      ``Entropy.pow_sqrt_mul_chainOptimum_le_logarithmic,
      ``Entropy.pow_sqrt_mul_norm_le_of_zero_floor_logarithmic] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
