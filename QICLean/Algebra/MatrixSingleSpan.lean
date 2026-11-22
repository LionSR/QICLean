/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Submodules of matrices containing every matrix unit

A submodule of the matrices over a semiring that contains every matrix unit `E_{ij}` is the
whole space, because every matrix is the sum of its entries times the matrix units. This is the
last step of a proof that a family of matrices spans the full matrix algebra: once every matrix
unit lies in the span, the span is everything.

## Main results

* `Submodule.eq_top_of_forall_single_mem`: a submodule containing every matrix unit is `⊤`.

Moved from TNLean, `TNLean/Algebra/MatrixSingleSpan.lean` at commit `49b78ed821`
(Apache-2.0). Changes: the motivating sentence is phrased for an arbitrary spanning family.
-/

namespace Submodule

/-- A submodule of matrices containing every matrix unit `E_{ij}` is the whole space. -/
theorem eq_top_of_forall_single_mem {R m n : Type*} [Semiring R] [Finite m] [Finite n]
    [DecidableEq m] [DecidableEq n] (T : Submodule R (Matrix m n R))
    (h : ∀ i j, Matrix.single i j (1 : R) ∈ T) : T = ⊤ := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  refine top_unique fun X _ => ?_
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using T.smul_mem (X i j) (h i j)

end Submodule
