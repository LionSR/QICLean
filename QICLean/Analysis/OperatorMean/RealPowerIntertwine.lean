/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MatrixPowers
import QICLean.Entropy.ConditionalMovement.LogCompression

/-!
# Rectangular intertwining of real matrix powers

The finite-dimensional functional calculus transports every real power
along a rectangular intertwiner of positive semidefinite matrices.

For a negative exponent, the power is zero on the kernel. No inverse on
that kernel is asserted.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `06-transport.tex`, lines 17–22 and 157–172, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: functional-calculus identities
  used in the geometric mean and its derivative.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Every real power transports along a rectangular intertwiner of positive
semidefinite matrices, with the spectral convention on the kernel. Auxiliary
to the geometric-mean calculations of OpenAI's area-law manuscript,
`06-transport.tex`, lines 17–22 and 157–172. -/
theorem PosSemidef.rpow_intertwine
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (J : Matrix n m ℂ)
    (hAJ : A * J = J * B) (s : ℝ) : A ^ s * J = J * B ^ s := by
  simpa only [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg] using
    ConditionalMovement.QuantumSSA.cfc_intertwine
      hA.isHermitian hB.isHermitian J hAJ (fun x : ℝ ↦ x ^ s)

end Matrix
