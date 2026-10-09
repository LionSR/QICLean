/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.PairMergeMoment
import QICLean.Representation.MergeExponential
import QICLean.Analysis.KroneckerExponential
import QICLean.Analysis.TraceDistance


/-!
# The two merge deficits on a common copy space

The actual Schur-label merge deficit on paired Q and C copies is
`F_Q + F_C - F_QC`. Its Hermiticity follows from the actual central label
observables. On the literal product of the QC and VR copy spaces, adjoining
identities gives two commuting Hermitian operators. Their exponentials
factor as a Kronecker product; each individual exponential trace is the
trace pairing with the corresponding actual partial trace. The common
matrix is arbitrary and may have correlations between the two pairs.

OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026), `07-comparators.tex`, lines 501–555,
`comparator:merge-decomposition` and `comparator:merge-moments`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All real exponential parameters,
zero copies and empty finite coordinate sets are included.

The actual component marginals, their moment bounds and the comparison of
complete metrics are separate assertions. In particular, the joint
exponential trace is not asserted to factor into two marginal traces.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/
/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition; comparator:merge-moments.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition; comparator:merge-moments.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition; comparator:merge-moments.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition; comparator:merge-moments.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition; comparator:merge-moments.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition; comparator:merge-moments.
-/

open Matrix PermutationRepresentation
open scoped Kronecker Matrix.Norms.Operator
namespace TensorPower
variable (Q C : Type*) [Fintype Q] [Fintype C] [DecidableEq Q] [DecidableEq C] (m : ℕ)
/-- The actual paired-copy merge deficit `F_Q + F_C - F_QC`, with all three
observables defined by the separate and simultaneous copy actions.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–506. -/
noncomputable def pairMergeDeficit :
    Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ :=
  labelEntropy (pairCopyLeft Q C m) + labelEntropy (pairCopyRight Q C m) -
    labelEntropy (pairCopyBoth Q C m)

/-- The actual paired-copy deficit is Hermitian.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–508. -/
theorem isHermitian_pairMergeDeficit : (pairMergeDeficit Q C m).IsHermitian := by
  exact ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
    (isHermitian_labelObservable _ _)

variable (V R : Type*) [Fintype V] [Fintype R] [DecidableEq V] [DecidableEq R]

/-- The QC and VR deficits commute on their literal common copy space.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–508. -/
theorem commute_pairMergeDeficit_lifts :
    Commute (pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ))
      ((1 : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ
        pairMergeDeficit V R m) := by
  change _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- The exponential of the two actual lifted deficits is their tensor-factor
exponential product. No matrix or invariance assumption is imposed.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–555. -/
theorem exp_pairMergeDeficit_lifts (a b : ℝ) :
    NormedSpace.exp ((a : ℂ) • (pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)) +
      (b : ℂ) • ((1 : Matrix ((Fin m → Q) × (Fin m → C))
        ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ pairMergeDeficit V R m)) =
      NormedSpace.exp ((a : ℂ) • pairMergeDeficit Q C m) ⊗ₖ
        NormedSpace.exp ((b : ℂ) • pairMergeDeficit V R m) := by
  rw [← Matrix.smul_kronecker, ← Matrix.kronecker_smul, Matrix.exp_kronecker_sum]

/-- The actual lifted QC exponential has the same complex trace pairing as
the local exponential against the actual QC partial trace. The common
matrix is arbitrary. OpenAI, September 24, 2026, `07-comparators.tex`,
lines 524–555, equation `comparator:merge-moments`. -/
theorem trace_exp_pairMergeDeficit_left
    (ρ : Matrix (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R)))
      (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R))) ℂ) (a : ℝ) :
    (ρ * NormedSpace.exp ((a : ℂ) • (pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)))).trace =
      (Matrix.partialTraceRight ρ * NormedSpace.exp ((a : ℂ) •
        pairMergeDeficit Q C m)).trace := by
  rw [← Matrix.smul_kronecker, Matrix.exp_kronecker_one,
    ← Matrix.trace_partialTraceRight_mul]

/-- The actual lifted VR exponential has the same complex trace pairing as
the local exponential against the actual VR partial trace. The common
matrix is arbitrary. OpenAI, September 24, 2026, `07-comparators.tex`,
lines 524–555, equation `comparator:merge-moments`. -/
theorem trace_exp_pairMergeDeficit_right
    (ρ : Matrix (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R)))
      (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R))) ℂ) (b : ℝ) :
    (ρ * NormedSpace.exp ((b : ℂ) • ((1 : Matrix ((Fin m → Q) × (Fin m → C))
      ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ pairMergeDeficit V R m))).trace =
      (Matrix.partialTraceLeft ρ * NormedSpace.exp ((b : ℂ) •
        pairMergeDeficit V R m)).trace := by
  rw [← Matrix.kronecker_smul, Matrix.exp_one_kronecker,
    ← Matrix.trace_partialTraceLeft_mul]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-decomposition.
-/

open scoped ComplexOrder in
/-- The actual paired-copy merge deficit is positive semidefinite. Separate
copy actions commute and their pointwise product is the simultaneous action,
so compatibility is derived from the actual label projections. OpenAI,
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 501–508, and Lemma 6.1(3), equation `replicas:merge-dimensions`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem posSemidef_pairMergeDeficit : (pairMergeDeficit Q C m).PosSemidef := by
  exact PermutationRepresentation.posSemidef_mergeDeficit (commute_pairCopy Q C m)
    (pairCopyBoth_eq_mul Q C m)

end TensorPower
