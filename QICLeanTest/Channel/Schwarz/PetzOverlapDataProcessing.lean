/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Schwarz.PetzOverlapDataProcessing
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Actual-name and boundary regressions for Wolf Equation (8.35). -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace PetzOverlapDataProcessingTest

noncomputable section

-- Singular, noncommuting trace-one states in dimension two.
def rho : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]
def sigma : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℝ) • vecMulVec (fun _ => (1 : ℂ)) (star (fun _ => (1 : ℂ)))

theorem rho_psd : rho.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem sigma_psd : sigma.PosSemidef :=
  (posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem rho_trace : rho.trace = 1 := by
  norm_num [rho, Matrix.trace, Fin.sum_univ_two]

theorem sigma_trace : sigma.trace = 1 := by
  norm_num [sigma, Matrix.trace, Fin.sum_univ_two, vecMulVec, Complex.real_smul]

example : rho.det = 0 ∧ sigma.det = 0 := by
  norm_num [rho, sigma, Matrix.det_fin_two, vecMulVec, Complex.real_smul]

example : rho * sigma ≠ sigma * rho := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [rho, sigma, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec,
    Complex.real_smul] at h01

-- These equal one, not the support-projection overlap of one half.
example : petzOverlap 0 rho sigma = 1 := by
  rw [petzOverlap_zero rho_psd sigma_psd, sigma_trace]
  rfl

example : petzOverlap 1 rho sigma = 1 := by
  rw [petzOverlap_one rho_psd sigma_psd, rho_trace]
  rfl

-- An actual rectangular CPTP preparation channel from dimension two to three.
def tau : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1, 0, 0]

theorem tau_psd : tau.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem tau_trace : tau.trace = 1 := by
  norm_num [tau, Matrix.trace, Fin.sum_univ_succ]

example {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (rho ^ s * sigma ^ (1 - s)).trace.re ≤
      ((preparationMap (α := Fin 2) tau rho) ^ s *
        (preparationMap (α := Fin 2) tau sigma) ^ (1 - s)).trace.re :=
  petzOverlap_data_processing hs (preparationMap_isKrausCPTP tau tau_psd tau_trace)
    rho_psd rho_trace sigma_psd sigma_trace

-- Arbitrary rectangular channels, in the raw source expression at both endpoints.
example (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ)
    (hT : IsKrausCPTP T) :
    (rho ^ (0 : ℝ) * sigma ^ (1 - (0 : ℝ))).trace.re ≤
      ((T rho) ^ (0 : ℝ) * (T sigma) ^ (1 - (0 : ℝ))).trace.re :=
  petzOverlap_data_processing (by norm_num) hT rho_psd rho_trace sigma_psd sigma_trace

example (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ)
    (hT : IsKrausCPTP T) :
    (rho ^ (1 : ℝ) * sigma ^ (1 - (1 : ℝ))).trace.re ≤
      ((T rho) ^ (1 : ℝ) * (T sigma) ^ (1 - (1 : ℝ))).trace.re :=
  petzOverlap_data_processing (by norm_num) hT rho_psd rho_trace sigma_psd sigma_trace

-- A singular density ancilla, including exponent endpoints.
example {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    petzOverlap s (rho ⊗ₖ tau) (sigma ⊗ₖ tau) = petzOverlap s rho sigma :=
  petzOverlap_tensor_density hs rho_psd sigma_psd tau_psd tau_trace

-- A genuine rectangular partial trace, without normalization or invertibility.
example {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ρ σ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    petzOverlap s ρ σ ≤ petzOverlap s (partialTraceRight ρ) (partialTraceRight σ) :=
  petzOverlap_le_partialTraceRight hs hρ hσ

-- The generic partial trace proof also permits an empty retained system.
example {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ρ σ : Matrix (Fin 0 × Fin 1) (Fin 0 × Fin 1) ℂ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    petzOverlap s ρ σ ≤ petzOverlap s (partialTraceRight ρ) (partialTraceRight σ) :=
  petzOverlap_le_partialTraceRight hs hρ hσ

end

end PetzOverlapDataProcessingTest

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.petzOverlap, ``Matrix.petzOverlap_zero,
    ``Matrix.petzOverlap_one, ``Matrix.petzOverlap_conj_unitary,
    ``Matrix.petzOverlap_reindex, ``Matrix.petzOverlap_tensor_density,
    ``Matrix.petzOverlap_le_map, ``Matrix.petzOverlap_data_processing,
    ``Matrix.petzOverlap_le_partialTraceRight,
    ``PetzOverlapDataProcessingTest.rho_psd, ``PetzOverlapDataProcessingTest.sigma_psd,
    ``PetzOverlapDataProcessingTest.rho_trace, ``PetzOverlapDataProcessingTest.sigma_trace,
    ``PetzOverlapDataProcessingTest.tau_psd, ``PetzOverlapDataProcessingTest.tau_trace]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
