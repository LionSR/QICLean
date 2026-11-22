/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Positive.QuantumChernoff
import QICLeanTest.Channel.PetzOverlapDataProcessing

/-! Boundary regressions and transitive axiom audit for finite-copy Chernoff bounds. -/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix PetzOverlapDataProcessingTest

noncomputable section

-- The existing two-dimensional pair is singular and noncommuting.
example {p s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) :
    optimalHypothesisTestError p (piKronecker (fun _ : Fin N ↦ rho))
      (piKronecker (fun _ : Fin N ↦ sigma)) ≤
        p ^ s * (1 - p) ^ (1 - s) * petzOverlap s rho sigma ^ N :=
  optimalHypothesisTestError_iid_le rho_psd sigma_psd rho_trace sigma_trace hp hs N

-- Degenerate priors really give zero optimal error, rather than requiring positive priors.
example : optimalHypothesisTestError 0 rho sigma = 0 := by
  apply le_antisymm
  · exact (optimalHypothesisTestError_le_min rho_psd.isHermitian sigma_psd.isHermitian
      rho_trace sigma_trace 0).trans (min_le_left _ _)
  · exact optimalHypothesisTestError_nonneg rho_psd sigma_psd rho_trace sigma_trace (by norm_num)

-- Endpoint overlap conventions remain valid after taking tensor powers.
example (N : ℕ) :
    petzOverlap 0 (piKronecker (fun _ : Fin N ↦ rho))
      (piKronecker (fun _ : Fin N ↦ sigma)) = 1 := by
  rw [petzOverlap_piKronecker _ _ (fun _ ↦ rho_psd) (fun _ ↦ sigma_psd)]
  simp [petzOverlap_zero rho_psd sigma_psd, sigma_trace]

-- With no samples even an empty local state space gives the one-dimensional identity.
example (s : ℝ) :
    petzOverlap s (piKronecker (fun _ : Fin 0 ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ)))
      (piKronecker (fun _ : Fin 0 ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ))) = 1 := by
  rw [petzOverlap_piKronecker _ _ (fun _ ↦ PosSemidef.zero) (fun _ ↦ PosSemidef.zero)]
  simp

-- Heterogeneous factors retain their own dimensions (two and three here).
example (s : ℝ) : petzOverlap s (rho ⊗ₖ tau) (sigma ⊗ₖ tau) =
    petzOverlap s rho sigma * petzOverlap s tau tau :=
  petzOverlap_kronecker rho_psd sigma_psd tau_psd tau_psd s

end

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.piKronecker_submatrix_cons, ``Matrix.piKronecker_mul,
    ``Matrix.trace_piKronecker, ``Matrix.rpow_piKronecker,
    ``Matrix.PosSemidef.rpow_submatrix_equiv, ``Matrix.PosSemidef.smul_rpow,
    ``Matrix.optimalHypothesisTestError, ``Matrix.optimalHypothesisTestError_eq,
    ``Matrix.exists_hypothesisTestError_eq_optimal, ``Matrix.optimalHypothesisTestError_le,
    ``Matrix.optimalHypothesisTestError_nonneg, ``Matrix.optimalHypothesisTestError_le_min,
    ``Matrix.petzOverlap_nonneg, ``Matrix.petzOverlap_smul, ``Matrix.petzOverlap_kronecker,
    ``Matrix.petzOverlap_piKronecker, ``Matrix.optimalHypothesisTestError_le_petzOverlap,
    ``Matrix.optimalHypothesisTestError_piKronecker_le,
    ``Matrix.optimalHypothesisTestError_iid_le, ``Matrix.optimalHypothesisTestError_iid_le_sInf,
    ``Matrix.optimalHypothesisTestError_iid_le_exp,
    ``Matrix.tendsto_optimalHypothesisTestError_iid_zero]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
