/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralFilter.FilterLocality

/-! Require every filter-locality theorem at named constants to use only standard axioms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``SpectralFilter.one_add_abs_pow_mul_abs_spectralKernel_le_kernelMomentBound,
      ``SpectralFilter.abs_spectralKernel_le_kernelTailConst,
      ``SpectralFilter.norm_filterIntegral_sub_map_le,
      ``SpectralFilter.norm_filterIntegral_sub_map_le_filterLocalityConst_mul,
      ``SpectralFilter.norm_positiveConstraint_sub_map_le,
      ``SpectralFilter.exists_norm_positiveConstraint_sub_map_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
