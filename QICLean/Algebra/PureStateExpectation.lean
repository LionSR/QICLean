/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Ring

/-!
# Expectations against a pure-state matrix

The expectation of a matrix in a vector equals its trace pairing with the outer product
of that vector. Trace pairings against all matrices determine a matrix uniquely.
No normalization or nonempty basis is required.
-/

public section

open Complex Matrix
open scoped InnerProductSpace

namespace Matrix

/-- An expectation is the trace against the pure-state matrix. -/
theorem inner_toEuclideanLin_eq_trace {m : Type*} [Fintype m] [DecidableEq m]
    (Y : Matrix m m ℂ) (ψ : EuclideanSpace ℂ m) :
    ⟪ψ, toEuclideanLin Y ψ⟫_ℂ = (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) * Y).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, toLpLin_apply, mulVec, dotProduct, trace,
    diag, mul_apply, vecMulVec_apply, Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [star_def]
  ring

/-- Matrices with the same trace pairing against every matrix are equal. -/
theorem eq_of_forall_trace_mul_eq {m : Type*} [Fintype m] {M N : Matrix m m ℂ}
    (h : ∀ A : Matrix m m ℂ, (M * A).trace = (N * A).trace) : M = N := by
  classical
  ext i j
  have hM : ∀ Y : Matrix m m ℂ, (Y * single j i (1 : ℂ)).trace = Y i j := fun Y ↦ by
    simp [trace, mul_apply, single_apply, ite_and, Finset.sum_ite_eq]
  rw [← hM M, ← hM N, h]

end Matrix
