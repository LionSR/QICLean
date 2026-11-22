/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Convexity.QuadraticPerspective
import QICLean.Channel.Convexity.TensorPowerConvexity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Proof-integrity checks for the perspective and tensor-power consequences of
Wolf Theorem 5.14. Check transitive dependencies, including the trace Ando--Lieb proofs. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.sum_conjTranspose_inv_mul_le,
      ``Matrix.conjTranspose_inv_mul_le_of_concave, ``Matrix.convexOn_quadraticPerspective,
      ``Matrix.convexOn_affine_quadraticPerspective,
      ``Matrix.conjTranspose_rpow_neg_mul_convex, ``Matrix.convexOn_conjTranspose_rpow_neg_mul,
      ``Matrix.sum_conjTranspose_rpow_neg_mul_le, ``Matrix.vec_transpose_kronecker_quadratic,
      ``Matrix.rpow_kronecker_rpow_concave, ``Matrix.rpow_kronecker_rpow_convex] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

-- The printed Hermitian-denominator claim in Corollary 5.4(1) is false
-- even for the scalar ordinary inverse, with L = 1 and equal weights.
example : ¬ (-3 / 2 : ℝ)⁻¹ ≤
    (1 / 2 : ℝ) * (-1 : ℝ)⁻¹ + (1 / 2 : ℝ) * (-2 : ℝ)⁻¹ := by
  norm_num
