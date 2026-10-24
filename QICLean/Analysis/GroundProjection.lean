/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.SpectralGap
import QICLean.Analysis.ShiftedDensityTruncation


/-!
# The ground projection from a global gap

A unit eigenvector and a strictly positive global gap identify the canonical
spectral projection below the excited-energy threshold with the rank-one
projection onto that vector. The identity includes a one-dimensional space
with an arbitrarily large positive gap parameter.

The proof compares both operators on an orthonormal eigenbasis and uses
the existing ground-or-excited dichotomy. It requires no spectral ceiling.

Sources: LVV, arXiv:1307.5143v1, lines 599–603, equation e:cutdown;
the OpenAI area-law manuscript, Theorem thm:area, 00-introduction.tex,
lines 44–47, and the polynomial-PEPS manuscript, equation eq:global-gap.
-/

open scoped InnerProductSpace ComplexOrder
open Matrix

private theorem cfc_basis_action
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) (k : n) :
    cfc f H *ᵥ WithLp.ofLp (hH.eigenvectorBasis k) =
      (f (hH.eigenvalues k) : ℂ) • WithLp.ofLp (hH.eigenvectorBasis k) := by
  rw [hH.cfc_eq, hH.cfc_form]
  rw [← mulVec_mulVec, hH.star_eigenvectorUnitary_mulVec, ← mulVec_mulVec,
    diagonal_mulVec_single, mul_one, mulVec_single]
  simp

/-- The canonical ground projection from the original global gap. Supporting spectral
identity for LVV, arXiv:1307.5143v1, `algo53.tex`, lines 599–603 (`e:cutdown`),
and the OpenAI area-law global gap, `thm:area`, `00-introduction.tex`, lines 44–47. -/
theorem Matrix.IsHermitian.complement_spectralProjectionGE_eq_rankOne
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ Δ : ℝ}
    {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : (H - (E₀ : ℂ) • 1 - (Δ : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) :
    1 - Matrix.spectralProjectionGE H (E₀ + Δ) =
      Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) := by
  apply Matrix.toEuclideanLin.injective
  refine hH.eigenvectorBasis.toBasis.ext fun k ↦ ?_
  rw [toEuclideanLin_vecMulVec_star_self_apply]
  apply (WithLp.ofLp_injective 2)
  change (1 - spectralProjectionGE H (E₀ + Δ)) *ᵥ WithLp.ofLp (hH.eigenvectorBasis k) =
    ⟪Ω, hH.eigenvectorBasis k⟫_ℂ • WithLp.ofLp Ω
  rw [sub_mulVec, one_mulVec, spectralProjectionGE, cfc_basis_action]
  rcases GaussianFilter.eigenvector_ground_or_gap hH hΩ hHΩ hgap hΔ k with
    ⟨hlam, hground⟩ | ⟨henergy, horth⟩
  · simpa [hlam, show ¬ E₀ + Δ ≤ E₀ by linarith] using congrArg WithLp.ofLp hground
  · simp [show E₀ + Δ ≤ hH.eigenvalues k by linarith, inner_eq_zero_symm.mpr horth]
