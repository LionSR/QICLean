/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralProjectionIntertwiner

/-!
# Spectral support from a compressed lower bound

If a Hermitian matrix commutes with an orthogonal projection and its compression
is bounded below by a real scalar times that projection, the projection's range
lies in the corresponding closed upper spectral subspace. The range may be zero,
and equality at the threshold is included.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `07-comparators.tex`, lines 481–493, `comparator:good-auxiliary`, at
  manuscript commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  This is an auxiliary finite-dimensional implication used in the label estimate.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.Operator

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A lower bound on a commuting compression gives closed spectral support
at the same threshold. Auxiliary to OpenAI's area-law manuscript,
`07-comparators.tex`, lines 481–493, `comparator:good-auxiliary`. -/
theorem spectralProjectionGE_shift_mul_eq_of_compression_lower
    {F P : Matrix n n ℂ} (hF : F.IsHermitian) (hP : IsStarProjection P)
    (hcomm : Commute F P) (c : ℝ)
    (hlower : (c : ℂ) • P ≤ P * F * P) :
    spectralProjectionGE (F - (c : ℂ) • 1) 0 * P = P := by
  have hB : (P * F * P - (c : ℂ) • P).PosSemidef := Matrix.le_iff.mp hlower
  have hshift : (F - (c : ℂ) • 1).IsHermitian :=
    hF.sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  apply spectralProjectionGE_zero_mul_of_intertwine hshift hB P
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    ← mul_assoc, hP.isIdempotentElem.eq]
  simp only [← hcomm.eq, mul_assoc, hP.isIdempotentElem.eq]

end Matrix
