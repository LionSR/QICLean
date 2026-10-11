/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalMovement.LogCompression

/-!
# A common positive compression on a fixed subspace

Let Z be an isometry with range projection P. If M P = P N and N commutes
with P, then M and N have the same action on the range of Z. When N is
positive definite, their common compression Zᴴ M Z = Zᴴ N Z is positive
definite and intertwines with both original matrices through Z.

The matrix M need not be Hermitian. The coordinate sets may be empty.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 80–110, 299–308 and
  370–381, `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- If an operator agrees on a fixed isometric range with a positive definite
operator preserving that range, their actual compressions coincide and are
positive definite. The same isometry intertwines both operators with this
common compression. No Hermitian assumption on M is required.

This is the finite-dimensional compression argument for the restricted
replica metrics in the area-law manuscript, `07-comparators.tex`, lines
80–110, 299–308 and 370–381, `comparator:pinned-metric`. -/
theorem PosDef.compression_of_projection_intertwine
    {M N P : Matrix m m ℂ} {Z : Matrix m n ℂ}
    (hN : N.PosDef) (hZ : Zᴴ * Z = 1) (hZZ : Z * Zᴴ = P)
    (hMP : M * P = P * N) (hNP : Commute N P) :
    let B := Zᴴ * M * Z
    B = Zᴴ * N * Z ∧ B.PosDef ∧
      M * Z = Z * B ∧ N * Z = Z * B := by
  intro B
  have hPZ : P * Z = Z := by
    rw [← hZZ, Matrix.mul_assoc, hZ, Matrix.mul_one]
  have hMZ : M * Z = N * Z := by
    calc
      M * Z = M * (P * Z) := by rw [hPZ]
      _ = (M * P) * Z := (Matrix.mul_assoc _ _ _).symm
      _ = (P * N) * Z := by rw [hMP]
      _ = N * Z := by rw [← hNP.eq, Matrix.mul_assoc, hPZ]
  have hcompression : B = Zᴴ * N * Z := by
    change Zᴴ * M * Z = Zᴴ * N * Z
    simpa only [Matrix.mul_assoc] using
      congrArg (fun L : Matrix m n ℂ ↦ Zᴴ * L) hMZ
  have hB : B.PosDef := by
    rw [hcompression]
    exact hN.conjTranspose_mul_mul_same
      (ConditionalMovement.QuantumSSA.isometry_mulVec_injective Z hZ)
  have hNZ : N * Z = Z * B := by
    calc
      N * Z = (P * N) * Z := by
        rw [← hNP.eq, Matrix.mul_assoc, hPZ]
      _ = (Z * Zᴴ) * N * Z := by rw [hZZ]
      _ = Z * (Zᴴ * N * Z) := by simp only [Matrix.mul_assoc]
      _ = Z * B := by rw [← hcompression]
  exact ⟨hcompression, hB, hMZ.trans hNZ, hNZ⟩

end Matrix
