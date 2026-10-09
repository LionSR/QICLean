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
  simpa only [Nat.cast_pow, mul_assoc, mul_left_comm] using
    (let hm := hρ.log_re_trace_finKronecker_signed_label_moments_le
        htr hmoment k hu hur hu1
     And.intro
       (huncentered u (K * (k : ℝ) * u ^ 2) (Real.le_exp_of_log_le hm.1))
       (huncentered (-u)
         (2 * K * (k : ℝ) * u ^ 2 +
           ((Fintype.card n : ℝ) ^ 2 / 2) * Real.log ((k : ℝ) + 1))
         (by simpa only [Complex.ofReal_neg] using Real.le_exp_of_log_le hm.2)))

end Matrix
