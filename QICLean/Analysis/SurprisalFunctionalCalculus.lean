/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Functional calculus of the negative matrix logarithm

For a finite Hermitian matrix, every real function is continuous on its
spectrum. Thus composition with the negative logarithm is valid even for a
discontinuous cutoff and even when the matrix has a kernel. Both sides use
the same convention `Real.log 0 = 0`.

The identity below specializes Mathlib's composition theorem. It also exposes
the composition step previously used locally in the tensor-power spectral-law
proof, without repeating that proof.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `07-comparators.tex`, lines 332–343, `comparator:rough-overlap`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- Functional calculus of the negative logarithm agrees with composition on
the original finite spectrum. No positivity, invertibility or continuity
hypothesis on the scalar function is required. For the strict upper cutoff,
this identifies the two trace-tail expressions used in the OpenAI area-law
manuscript, `07-comparators.tex`, lines 339–343. -/
theorem IsHermitian.cfc_neg_log_eq
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (-CFC.log A) = hA.cfc (fun u ↦ f (-Real.log u)) := by
  rw [CFC.log, ← cfc_neg, ← hA.cfc_eq]
  exact (cfc_comp' f (fun u : ℝ ↦ -Real.log u) A
    ((A.finite_real_spectrum.image _).continuousOn f)
    (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint).symm

end Matrix
