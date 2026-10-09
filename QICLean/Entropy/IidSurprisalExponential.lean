/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SurprisalProductMoment
import QICLean.Entropy.IidSurprisal

/-!
# Exact centered exponential moments of tensor-power densities

The weighted exponential of the actual tensor-power surprisal has the
product moment of the original eigenvalue weights. A scalar center is
arbitrary. Neither invertibility nor trace-one normalization is required
for this identity; zero eigenvalues carry zero weight.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 218--238,
`comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Centering and scaling a Hermitian matrix in the exponential agree
with the corresponding scalar functional calculus. Source:
`07-comparators.tex`, lines 218--238. -/
theorem IsHermitian.exp_smul_sub_smul_one_eq_cfc
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (u s : ℝ) :
    NormedSpace.exp ((u : ℂ) • (A - (s : ℂ) • 1)) =
      cfc (fun x : ℝ ↦ Real.exp (u * (x - s))) A := by
  simp only [Complex.coe_smul]
  rw [cfc_comp' Real.exp (fun x : ℝ ↦ u * (x - s)) A (ha := hA.isSelfAdjoint)]
  rw [cfc_const_mul u (fun x : ℝ ↦ x - s) A (by fun_prop),
    cfc_sub (fun x : ℝ ↦ x) (fun _ ↦ s) A (by fun_prop) (by fun_prop),
    cfc_id' ℝ A hA.isSelfAdjoint,
    cfc_const s A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  exact (CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all u).smul
    (hA.isSelfAdjoint.sub ((IsSelfAdjoint.all s).smul IsSelfAdjoint.one)))).symm

/-- The actual centered tensor-power surprisal moment is the power of
the one-copy moment times its scalar centering factor. Singular and zero
densities, arbitrary centers and zero copies are included. Source:
`07-comparators.tex`, lines 218--238. -/
theorem PosSemidef.re_trace_finKronecker_exp_centered_surprisal
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (k : ℕ) (u s : ℝ) :
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    (ρk * NormedSpace.exp ((u : ℂ) • (-CFC.log ρk - (s : ℂ) • 1))).trace.re =
      Real.exp (-u * s) * Entropy.surprisalMoment hρ.isHermitian.eigenvalues u ^ k := by
  intro ρk
  rw [(show (-CFC.log ρk).IsHermitian from IsSelfAdjoint.log.neg).exp_smul_sub_smul_one_eq_cfc,
    hρ.re_trace_finKronecker_mul_cfc_surprisal k (fun x ↦ Real.exp (u * (x - s)))]
  rw [← Entropy.surprisalMoment_pi hρ.isHermitian.eigenvalues k u]
  simp_rw [Entropy.surprisalMoment, Finset.mul_sum, mul_sub, sub_eq_add_neg, Real.exp_add]
  done

end Matrix
