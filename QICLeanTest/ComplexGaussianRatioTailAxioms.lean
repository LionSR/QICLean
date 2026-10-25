/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.RatioTail
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the lower tail of a complex Gaussian coordinate ratio. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``QICLean.ComplexGaussian.integral_exp_mul_sq_gaussianReal,
    ``QICLean.ComplexGaussian.integrable_exp_mul_sq_gaussianReal,
    ``QICLean.ComplexGaussian.norm_coordinate_sq,
    ``QICLean.ComplexGaussian.integrable_exp_sum_mul_norm_coordinate_sq,
    ``QICLean.ComplexGaussian.integral_exp_sum_mul_norm_coordinate_sq,
    ``QICLean.ComplexGaussian.integral_exp_mul_norm_coordinate_sq,
    ``QICLean.ComplexGaussian.measureReal_sum_norm_coordinate_sq_le_le,
    ``QICLean.ComplexGaussian.measure_sum_norm_coordinate_sq_le_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
