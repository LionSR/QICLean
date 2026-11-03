/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceCFC

/-!
# Functional calculus on the actual Hermitian eigenbasis

The matrix functional calculus acts on the canonical eigenbasis by applying
the scalar function to its actual eigenvalues. This is the diagonal form of
the finite-dimensional spectral theorem. It supports the spectral filters in
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1620–1643, and LVV,
arXiv:1307.5143v1, equation `e:cutdown`, lines 599–603.
-/

open Matrix

/-- Functional calculus evaluated on the actual Hermitian eigenbasis.
This is Mathlib's Hermitian functional calculus in eigenvector coordinates;
it supports ALVV, arXiv:1602.08828v2, final spectral filter, lines 1620–1643. -/
theorem Matrix.IsHermitian.cfc_mulVec_eigenvectorBasis
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) (k : n) :
    cfc f H *ᵥ WithLp.ofLp (hH.eigenvectorBasis k) =
      (f (hH.eigenvalues k) : ℂ) • WithLp.ofLp (hH.eigenvectorBasis k) := by
  rw [hH.cfc_eq, hH.cfc_form]
  rw [← Matrix.mulVec_mulVec, hH.star_eigenvectorUnitary_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.diagonal_mulVec_single, mul_one, Matrix.mulVec_single]
  simp
