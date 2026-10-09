/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.IidSurprisalExponential
import QICLean.Representation.SchurLabelMomentBounds
import QICLean.Algebra.PiProductTrace

/-!
# Signed Schur moments from one-copy surprisal moments

The exact tensor-power moment identity transfers a one-copy logarithmic
surprisal bound to the actual independent-copy density. Applying the
centered Schur comparison gives both signs of the label entropy, with
the explicit negative-sign polynomial remainder. Singular densities
and zero copies are included.

Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 75–85 and 218–238, `comparator:mgf-data` and
`comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- The logarithm of the actual centered tensor-power moment is additive
in the number of copies. The trace-one assumption makes the scalar
moment strictly positive, including for singular densities. Source:
`07-comparators.tex`, lines 75–85 and 227–238. -/
theorem PosSemidef.log_re_trace_finKronecker_exp_centered_surprisal
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (k : ℕ) (u s : ℝ) :
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    Real.log (ρk * NormedSpace.exp ((u : ℂ) •
      (-CFC.log ρk - (s : ℂ) • 1))).trace.re =
        -u * s + (k : ℝ) *
          Real.log (Entropy.surprisalMoment hρ.isHermitian.eigenvalues u) := by
  rw [hρ.re_trace_finKronecker_exp_centered_surprisal,
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _
      (Entropy.surprisalMoment_pos hρ.eigenvalues_nonneg
        (posSemidef_trace_one_eigenvalues_sum_one hρ htr) u).ne'),
    Real.log_exp, Real.log_pow]

/-- A one-copy logarithmic surprisal bound gives both centered Schur
moments of the actual tensor-power density. The negative sign has
twice the quadratic coefficient and the stated polynomial remainder.
Source: `07-comparators.tex`, `comparator:mgf-data` and
`comparator:signed-label-moments`, lines 75–85 and 227–238. -/
theorem PosSemidef.log_re_trace_finKronecker_signed_label_moments_le
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {K r : ℝ}
    (hmoment : ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment hρ.isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy ρ hρ.isHermitian + K * v ^ 2)
    (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (hur : 2 * u ≤ r) (hu1 : 2 * u ≤ 1) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    Real.log (ρk * NormedSpace.exp ((u : ℂ) •
      (labelEntropy (copyPerm n k) - (((k : ℝ) * S : ℝ) : ℂ) • 1))).trace.re ≤
        K * k * u ^ 2 ∧
    Real.log (ρk * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm n k) - (((k : ℝ) * S : ℝ) : ℂ) • 1))).trace.re ≤
        2 * K * k * u ^ 2 + ((Fintype.card n : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  simpa only [mul_one, Real.sqrt_one, div_one] using
    (TensorPower.log_centered_labelEntropy_moments_le
      (finKronecker_posSemidef (fun _ : Fin k ↦ ρ) (fun _ ↦ hρ)) ?_
      (fun σ ↦ (commute_finKronecker_const_permOp ρ k σ).symm)
      ((k : ℝ) * vonNeumannEntropy ρ hρ.isHermitian) K r 1 le_rfl ?_ u hu ?_)
  all_goals done

end Matrix
