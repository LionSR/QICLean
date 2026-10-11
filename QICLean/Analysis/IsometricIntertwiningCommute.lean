/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Complex.Basic

/-!
# Commutation in isometric coordinates

Two commuting matrices induce commuting matrices on a common isometric
invariant subspace. Neither matrix needs to be Hermitian.

This elementary observation is used for the restricted band metrics in
OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 268–276, and `07-comparators.tex`,
`comparator:nesting`, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Commutation descends through a common isometric intertwiner.
Auxiliary to the symmetric-space commutation of the area-law manuscript,
`06-transport.tex`, lines 268–276. -/
theorem commute_of_isometric_intertwine
    {M N : Matrix m m ℂ} {B C : Matrix n n ℂ} {Z : Matrix m n ℂ}
    (hZ : Zᴴ * Z = 1) (hM : M * Z = Z * B) (hN : N * Z = Z * C)
    (hMN : Commute M N) : Commute B C := by
  have hprod : Z * (B * C) = Z * (C * B) := by
    calc
      Z * (B * C) = (Z * B) * C := (Matrix.mul_assoc _ _ _).symm
      _ = (M * Z) * C := by rw [hM]
      _ = M * (Z * C) := Matrix.mul_assoc _ _ _
      _ = M * (N * Z) := by rw [hN]
      _ = (M * N) * Z := (Matrix.mul_assoc _ _ _).symm
      _ = (N * M) * Z := by rw [hMN.eq]
      _ = N * (M * Z) := Matrix.mul_assoc _ _ _
      _ = N * (Z * B) := by rw [hM]
      _ = (N * Z) * B := (Matrix.mul_assoc _ _ _).symm
      _ = (Z * C) * B := by rw [hN]
      _ = Z * (C * B) := Matrix.mul_assoc _ _ _
  change B * C = C * B
  simpa only [← Matrix.mul_assoc, hZ, Matrix.one_mul] using
    congrArg (fun L : Matrix m n ℂ ↦ Zᴴ * L) hprod

end Matrix
