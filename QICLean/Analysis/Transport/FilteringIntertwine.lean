/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs
import QICLean.Analysis.OperatorMean.RealPowerIntertwine
import QICLean.Algebra.MatrixAux

/-!
# Filtering along a rectangular intertwiner

Real powers transport the unnormalized filtered vector along an intertwiner.
An isometry also preserves its squared norm, so the normalized formula uses
exactly the same scalar on the two spaces. These identities include the
zero-vector case; a unit-norm assertion requires a nonzero denominator.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, 06-transport.tex, transport:filtered-vector, lines 388–392,
  revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.Transport

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The unnormalized filtered vector respects a rectangular intertwiner.
Auxiliary to OpenAI's area-law manuscript, 06-transport.tex,
transport:filtered-vector, lines 388–392. For semidefinite inputs, negative
powers use the spectral convention of vanishing on the kernel. -/
theorem filteredRaw_intertwine {M : Matrix n n ℂ} {N : Matrix m m ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) (J : Matrix n m ℂ)
    (hJ : M * J = J * N) (pre : m → ℂ) :
    filteredRaw M (J *ᵥ pre) = J *ᵥ filteredRaw N pre := by
  simpa only [filteredRaw, mulVec_mulVec] using
    congrArg (fun K : Matrix n m ℂ ↦ K *ᵥ pre)
      (hM.rpow_intertwine hN J hJ (-(1 / 4) : ℝ))

/-- An isometric intertwiner preserves the squared filtering norm.
Auxiliary to OpenAI's area-law manuscript, 06-transport.tex,
transport:filtered-vector, lines 388–392. No nonzero-vector premise is needed. -/
theorem filteredNormSq_intertwine {M : Matrix n n ℂ} {N : Matrix m m ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) (J : Matrix n m ℂ)
    (hJ : M * J = J * N) (hIsom : Jᴴ * J = 1) (pre : m → ℂ) :
    filteredNormSq M (J *ᵥ pre) = filteredNormSq N pre := by
  simp only [filteredNormSq, filteredRaw_intertwine hM hN J hJ pre,
    star_dotProduct_mulVec, mulVec_mulVec, hIsom, one_mulVec]

/-- An isometric intertwiner transports the normalized filtering formula.
Auxiliary to OpenAI's area-law manuscript, 06-transport.tex,
transport:filtered-vector, lines 388–392. At a zero denominator both formulas
are zero, with the total reciprocal convention. -/
theorem filteredVector_intertwine {M : Matrix n n ℂ} {N : Matrix m m ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) (J : Matrix n m ℂ)
    (hJ : M * J = J * N) (hIsom : Jᴴ * J = 1) (pre : m → ℂ) :
    filteredVector M (J *ᵥ pre) = J *ᵥ filteredVector N pre := by
  simp only [filteredVector, filteredNormSq_intertwine hM hN J hJ hIsom pre,
    filteredRaw_intertwine hM hN J hJ pre, mulVec_smul]

end Matrix.Transport
