/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Typical.IidSurprisalMomentExponential
import QICLean.Representation.Replica.PermutationCovariance
import QICLean.Representation.Permutation.SchurLabelMomentBounds
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity

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
theorem PosSemidef.log_re_trace_piKronecker_exp_centered_surprisal
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (k : ℕ) (u s : ℝ) :
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    Real.log (ρk * NormedSpace.exp ((u : ℂ) •
      (-CFC.log ρk - (s : ℂ) • 1))).trace.re =
        -u * s + (k : ℝ) *
          Real.log (Entropy.surprisalMoment hρ.isHermitian.eigenvalues u) := by
  dsimp only
  rw [hρ.re_trace_piKronecker_exp_centered_surprisal,
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _
      (Entropy.surprisalMoment_pos hρ.eigenvalues_nonneg
        (posSemidef_trace_one_eigenvalues_sum_one hρ htr) u).ne'),
    Real.log_exp, Real.log_pow]

/-- A one-copy logarithmic surprisal bound gives both centered Schur
moments of the actual tensor-power density. The negative sign has
twice the quadratic coefficient and the stated polynomial remainder.
Source: `07-comparators.tex`, `comparator:mgf-data` and
`comparator:signed-label-moments`, lines 75–85 and 227–238. -/
theorem PosSemidef.log_re_trace_piKronecker_signed_label_moments_le
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {K r : ℝ}
    (hmoment : ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment hρ.isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy ρ hρ.isHermitian + K * v ^ 2)
    (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (hur : 2 * u ≤ r) (hu1 : 2 * u ≤ 1) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    Real.log (ρk * NormedSpace.exp ((u : ℂ) •
      (labelEntropy (copyPerm n k) - (((k : ℝ) * S : ℝ) : ℂ) • 1))).trace.re ≤
        K * k * u ^ 2 ∧
    Real.log (ρk * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm n k) - (((k : ℝ) * S : ℝ) : ℂ) • 1))).trace.re ≤
        2 * K * k * u ^ 2 + ((Fintype.card n : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  simpa only [mul_one, Real.sqrt_one, div_one] using
    (TensorPower.log_centered_labelEntropy_moments_le
      (piKronecker_posSemidef (fun _ : Fin k ↦ ρ) (fun _ ↦ hρ))
      (by
        change Matrix.trace (fun x y : Fin k → n ↦ ∏ j, ρ (x j) (y j)) = 1
        simpa only [htr, Finset.prod_const_one] using
          trace_piProduct (fun _ : Fin k ↦ ρ))
      (fun σ ↦ (commute_piKronecker_const_permOp ρ k σ).symm)
      ((k : ℝ) * vonNeumannEntropy ρ hρ.isHermitian) K r 1 le_rfl
      (by
        intro v hv
        rw [hρ.log_re_trace_piKronecker_exp_centered_surprisal htr k v
          ((k : ℝ) * vonNeumannEntropy ρ hρ.isHermitian), mul_one]
        nlinarith only [mul_le_mul_of_nonneg_left
          (hmoment v (by simpa only [Real.sqrt_one, div_one] using hv))
          (Nat.cast_nonneg k)]) u hu
      (by simpa only [Real.sqrt_one, div_one,
        le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, mul_comm u 2] using
        And.intro hur hu1))

end Matrix

section IidSchurExponentialMoments

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
theorem PosSemidef.re_trace_piKronecker_exp_signed_labelEntropy_le
    {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {K r : ℝ}
    (hmoment : ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment hρ.isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy ρ hρ.isHermitian + K * v ^ 2)
    (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (hur : 2 * u ≤ r) (hu1 : 2 * u ≤ 1) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    (ρk * NormedSpace.exp ((u : ℂ) • labelEntropy (copyPerm n k))).trace.re ≤
      Real.exp (u * ((k : ℝ) * S) + (k : ℝ) * K * u ^ 2) ∧
    (ρk * NormedSpace.exp (((-u : ℝ) : ℂ) • labelEntropy (copyPerm n k))).trace.re ≤
      Real.exp ((-u) * ((k : ℝ) * S) + (2 * (k : ℝ) * K * u ^ 2 +
        ((Fintype.card n ^ 2 : ℕ) : ℝ) / 2 * Real.log ((k : ℝ) + 1))) := by
  intro S ρk
  have hshift (a : ℝ) :
      NormedSpace.exp ((a : ℂ) • labelEntropy (copyPerm n k)) =
        Real.exp (a * ((k : ℝ) * S)) •
          NormedSpace.exp ((a : ℂ) • (labelEntropy (copyPerm n k) -
            (((k : ℝ) * S : ℝ) : ℂ) • 1)) := by
    rw [(posSemidef_labelEntropy (copyPerm n k)).isHermitian.exp_smul_sub_smul_one_eq_cfc]
    have hzero : NormedSpace.exp ((a : ℂ) • labelEntropy (copyPerm n k)) =
        cfc (fun x : ℝ ↦ Real.exp (a * x)) (labelEntropy (copyPerm n k)) := by
      simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using
        (posSemidef_labelEntropy (copyPerm n k)).isHermitian.exp_smul_sub_smul_one_eq_cfc a 0
    rw [hzero, ← cfc_const_mul (Real.exp (a * ((k : ℝ) * S)))
      (fun x : ℝ ↦ Real.exp (a * (x - (k : ℝ) * S)))
      (labelEntropy (copyPerm n k)) (by fun_prop)]
    simp_rw [mul_sub, Real.exp_sub, mul_div_cancel₀ _ (Real.exp_ne_zero _)]
  have huncentered (a E : ℝ)
      (hcenter : (ρk * NormedSpace.exp ((a : ℂ) •
        (labelEntropy (copyPerm n k) - (((k : ℝ) * S : ℝ) : ℂ) • 1))).trace.re ≤
          Real.exp E) :
      (ρk * NormedSpace.exp ((a : ℂ) • labelEntropy (copyPerm n k))).trace.re ≤
        Real.exp (a * ((k : ℝ) * S) + E) := by
    rw [hshift a, mul_smul_comm, trace_smul, Complex.smul_re, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left hcenter (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  simpa only [Nat.cast_pow, mul_comm K (k : ℝ),
    show (2 : ℝ) * K * k = 2 * k * K by ring] using
    (let hm := hρ.log_re_trace_piKronecker_signed_label_moments_le
        htr hmoment k hu hur hu1
     And.intro
       (huncentered u (K * (k : ℝ) * u ^ 2) (Real.le_exp_of_log_le hm.1))
       (huncentered (-u)
         (2 * K * (k : ℝ) * u ^ 2 +
           ((Fintype.card n : ℝ) ^ 2 / 2) * Real.log ((k : ℝ) + 1))
         (by simpa only [Complex.ofReal_neg] using Real.le_exp_of_log_le hm.2)))

end Matrix
end

end IidSchurExponentialMoments
