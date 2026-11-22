/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Mixed density matrices of finite weighted operator sums

Conjugating a matrix `ρ` by two finite weighted sums `∑ a, c a • K a` and `∑ b, d b • L b`
gives the double sum of the mixed terms `K a ρ (L b)ᴴ`, with the bra coefficients conjugated.

Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Moved from TNLean, `TNLean/Algebra/MatrixDensitySum.lean` at commit `49b78ed821` (Apache-2.0).
-/

open scoped Matrix ComplexConjugate

namespace Matrix

/-- A finite sum on each side of a rectangular input matrix gives the mixed
ket–bra sum with the bra coefficients conjugated. -/
theorem sum_smul_mul_mul_conjTranspose {α β m n p q : Type*}
    [Fintype α] [Fintype β] [Fintype n] [Fintype q]
    (c : α → ℂ) (d : β → ℂ) (K : α → Matrix m n ℂ)
    (L : β → Matrix p q ℂ) (ρ : Matrix n q ℂ) :
    (∑ a, c a • K a) * ρ * (∑ b, d b • L b)ᴴ =
      ∑ a, ∑ b, (c a * conj (d b)) • (K a * ρ * (L b)ᴴ) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul, Complex.star_def]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end Matrix
