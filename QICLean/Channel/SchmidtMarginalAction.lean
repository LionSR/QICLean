/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.SchmidtTrimming

/-!
# The left marginal after an operator on the left factor

Multiplication on the first factor conjugates the left marginal. This
identity supports the collective trimming of ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
-/

namespace Matrix

/-- The reduced operator after acting on the first factor is the
conjugate of the original reduced operator. Used in ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_leftApply {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (w : EuclideanSpace ℂ (m × n)) :
    leftMarginal (leftApply A w) = A * leftMarginal w * Aᴴ := by
  classical
  simp only [leftMarginal, schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul,
    Matrix.mul_assoc]

end Matrix
