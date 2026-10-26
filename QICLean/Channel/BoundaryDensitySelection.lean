/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.BoundaryDensityMinimizer
import QICLean.Analysis.DensityMaxEigenvector

/-!
# A leading eigenvector of a minimizing feasible density matrix

A nonempty density set with support and boundary constraints admits a global minimum
of the left energy. A unit eigenvector for the largest eigenvalue of a minimizing
density matrix is fixed by the same support matrix: its eigenvalue is positive, so
the support identity for the density matrix can be cancelled on this eigenvector.

This is an auxiliary existence statement for the size-trimming optimization problem
of Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–476, and the leading eigenvector in Lemma 2.5 (`l:leading`), lines 493–505.
-/

open scoped Matrix Kronecker ComplexOrder

namespace Matrix

variable {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
  [DecidableEq s] [DecidableEq b]

/-- A global minimum over the feasible densities has a positive maximal-eigenvalue
unit vector fixed by the support matrix. Auxiliary existence for LVV13, `algo53.tex`,
equation `eq:conv`, lines 472–476, and Lemma 2.5, lines 493–505. -/
theorem exists_boundary_density_minimizer_max_eigenvector
    (P HL : Matrix (a × s) (a × s) ℂ) (X : Matrix (s × b) (s × b) ℂ) (η : ℝ)
    (hne : Set.Nonempty {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ ∧
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}) :
    ∃ (σ : Matrix ((a × s) × b) ((a × s) × b) ℂ)
      (u : EuclideanSpace ℂ ((a × s) × b)) (μ : ℝ),
      σ.PosSemidef ∧ σ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * σ = σ ∧
      rectangularTraceNorm (partialTraceFirst σ - X) ≤ η ∧
      (∀ ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ →
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η →
        (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
          (ρ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re) ∧
      ‖u‖ = 1 ∧ 0 < μ ∧ σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧
      (P ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
      ∀ (ν : ℝ) (w : EuclideanSpace ℂ ((a × s) × b)), w ≠ 0 →
        σ *ᵥ WithLp.ofLp w = (ν : ℂ) • WithLp.ofLp w → ν ≤ μ := by
  obtain ⟨σ, hσ, htr, hP, hX, hmin⟩ :=
    exists_boundary_density_minimizer_of_nonempty P HL X η hne
  obtain ⟨u, μ, hu, heig, hμ, hmax⟩ := hσ.exists_unit_eigenvector_max_eigenvalue htr
  refine ⟨σ, u, μ, hσ, htr, hP, hX, hmin, hu, hμ, heig, ?_, hmax⟩
  apply smul_right_injective _ (show (μ : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hμ)
  simpa only [← mulVec_mulVec, heig, mulVec_smul] using
    congrArg (fun A ↦ A *ᵥ WithLp.ofLp u) hP

end Matrix
