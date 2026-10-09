/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.IidSchurSignedMoments

/-!
# Uncentered signed exponential moments of independent-copy Schur labels

Extracting the scalar entropy center from the matrix exponential turns
the centered signed Schur bounds into uncentered bounds. The one-copy
logarithmic surprisal hypothesis is retained, including for singular
density matrices and zero copies.

Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 218–238 and 550–560, `comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open PermutationRepresentation TensorPower
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

/-- The two signed exponential moments retain the original entropy center
and the exact negative-sign polynomial remainder. The one-copy logarithmic
surprisal bound is an explicit hypothesis. Source: `07-comparators.tex`,
lines 218–238 and 550–560. -/
theorem PosSemidef.re_trace_finKronecker_exp_signed_labelEntropy_le
    {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {K r : ℝ}
    (hmoment : ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment hρ.isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy ρ hρ.isHermitian + K * v ^ 2)
    (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (hur : 2 * u ≤ r) (hu1 : 2 * u ≤ 1) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    (ρk * NormedSpace.exp ((u : ℂ) • labelEntropy (copyPerm n k))).trace.re ≤
      Real.exp (u * ((k : ℝ) * S) + (k : ℝ) * K * u ^ 2) ∧
    (ρk * NormedSpace.exp (((-u : ℝ) : ℂ) • labelEntropy (copyPerm n k))).trace.re ≤
      Real.exp ((-u) * ((k : ℝ) * S) + (2 * (k : ℝ) * K * u ^ 2 +
        ((Fintype.card n ^ 2 : ℕ) : ℝ) / 2 * Real.log ((k : ℝ) + 1))) := by
  intro S ρk
  done

end Matrix
