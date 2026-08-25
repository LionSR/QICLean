/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace of a dependent product matrix

This file proves that the trace of a matrix indexed by a dependent product and
formed entrywise from a finite family of matrices is the product of the traces
of those matrices.
-/

open scoped BigOperators

namespace Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
  {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The trace of a matrix whose entries are dependent products of matrix
entries is the product of the traces of its factors. -/
theorem trace_piProduct (P : (i : ι) → Matrix (α i) (α i) R) :
    trace (fun (x y : ∀ i, α i) ↦ ∏ i, P i (x i) (y i)) =
      ∏ i, trace (P i) := by
  simp only [trace, diag]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum (fun _ ↦ Finset.univ) fun i x ↦ P i x x]

end Matrix
