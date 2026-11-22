/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian eigenvectors in Euclidean space

The finite-dimensional spectral theorem gives an orthonormal eigenbasis of
a Hermitian matrix. Its eigenvector equation is stated here for the
continuous linear action on Euclidean space. This is the Euclidean form of
`Matrix.IsHermitian.mulVec_eigenvectorBasis` in Mathlib's
`Analysis/Matrix/Spectrum.lean`; it supplies the spectral coordinates used
in ALVV, arXiv:1602.08828v2, Lemma `lem:hard-trunc`, lines 955–968.
-/

namespace Matrix.IsHermitian

/-- A Hermitian matrix acts diagonally on its chosen Euclidean eigenbasis.
This is Mathlib's spectral-theorem identity
`Matrix.IsHermitian.mulVec_eigenvectorBasis`, expressed as a continuous
linear map on Euclidean space. It is used in the low-energy comparisons
of ALVV, arXiv:1602.08828v2, Lemma `lem:hard-trunc`, lines 955–968. -/
theorem toEuclideanCLM_eigenvectorBasis
    {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (j : n) :
    Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) A (hA.eigenvectorBasis j) =
      (hA.eigenvalues j : 𝕜) • hA.eigenvectorBasis j := by
  apply WithLp.ofLp_injective 2
  simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using hA.mulVec_eigenvectorBasis j

end Matrix.IsHermitian
