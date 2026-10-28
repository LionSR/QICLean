/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevSpectralFilter
import QICLean.Analysis.GroundProjection

/-!
# A Chebyshev filter from a unit ground vector and a global gap

The real polynomial is constructed from the actual Hermitian Hamiltonian and its
spectral ceiling. A unit ground vector and a positive global gap identify its canonical
low-energy projection with the rank-one ground projection. The same filter fixes that
vector and preserves its orthogonal complement, with the explicit squared shrinking
coefficient of the normalized Chebyshev construction.

Source: AKLV, arXiv:1301.1162v1, Section 4, Lemma 4.1, lines 530--583,
and the approximate-ground-space-projector conditions preceding that lemma.
No locality, operator Schmidt rank or entropy statement is assumed here.
-/

open Matrix Polynomial
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- The actual Chebyshev polynomial fixes the given unit ground vector, preserves its
orthogonal complement and has explicit norm and squared shrinking bounds.
AKLV, arXiv:1301.1162v1, Section 4, Lemma 4.1, lines 530--583. -/
theorem IsHermitian.exists_chebyshev_ground_filter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {E0 gap u : ℝ}
    {Γ : EuclideanSpace ℂ ι} (hΓ : ‖Γ‖ = 1)
    (hHΓ : H *ᵥ WithLp.ofLp Γ = (E0 : ℂ) • WithLp.ofLp Γ)
    (hgap : (H - (E0 : ℂ) • 1 - (gap : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef)
    (hgap0 : 0 < gap) (hgu : E0 + gap ≤ u)
    (hupper : ∀ x ∈ spectrum ℝ H, x ≤ u) (ell : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E0 = 1 ∧
      let K : Matrix ι ι ℂ := Polynomial.aeval H p
      toEuclideanLin K Γ = Γ ∧
      ‖K - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
        2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt (gap / (u - E0))) ∧
      ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
        ‖toEuclideanLin K ψ‖ ^ 2 ≤
          (2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt (gap / (u - E0)))) ^ 2 := by
  have hspectrum : ∀ x ∈ spectrum ℝ H, x = E0 ∨ x ∈ Set.Icc (E0 + gap) u := by
    intro x hx
    obtain ⟨j, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hx
    exact (GaussianFilter.eigenvector_ground_or_gap hH hΓ hHΓ hgap hgap0 j).elim
      (fun hg ↦ Or.inl hg.1)
      (fun he ↦ Or.inr ⟨by linarith [he.1], hupper _ hx⟩)
  obtain ⟨p, hdegree, hp0, hPg, hKPg, hPgK, herror⟩ :=
    hH.exists_polynomial_approximating_isolated_energy_projection ell
      (a := E0) (b := E0 + gap) (u := u) (by linarith) hgu hspectrum
  have hcanonical := hH.complement_spectralProjectionGE_eq_rankOne hΓ hHΓ hgap hgap0
  rw [hcanonical] at hKPg hPgK herror
  let K : Matrix ι ι ℂ := Polynomial.aeval H p
  let P := vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))
  change K * P = P at hKPg
  change P * K = P at hPgK
  have herr : ‖K - P‖ ≤ 2 * Real.exp
      (-2 * (ell : ℝ) * Real.sqrt (gap / (u - E0))) := by
    simpa only [add_sub_cancel_left] using herror
  have hPΓ : toEuclideanLin P Γ = Γ := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, inner_self_eq_norm_sq_to_K, hΓ]
  have hKΓ : toEuclideanLin K Γ = Γ := by
    simpa only [toEuclideanLin_mul, LinearMap.comp_apply, hPΓ] using
      congrArg (fun T : Matrix ι ι ℂ ↦ toEuclideanLin T Γ) hKPg
  refine ⟨p, hdegree, hp0, hKΓ, herr, ?_⟩
  intro ψ hψ horth
  have hPψ : toEuclideanLin P ψ = 0 := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, horth]
  have hPKψ : ⟪Γ, toEuclideanLin K ψ⟫_ℂ • Γ = 0 := by
    simpa only [toEuclideanLin_mul, LinearMap.comp_apply, P,
      toEuclideanLin_vecMulVec_star_self_apply, hPψ] using
        congrArg (fun T : Matrix ι ι ℂ ↦ toEuclideanLin T ψ) hPgK
  have hΓne : Γ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_ne_one] at hΓ
  have hinner : ⟪Γ, toEuclideanLin K ψ⟫_ℂ = 0 :=
    (smul_eq_zero.mp hPKψ).resolve_right hΓne
  have hn : ‖toEuclideanLin (K - P) ψ‖ ≤ ‖K - P‖ * ‖ψ‖ :=
    (toEuclideanCLM (n := ι) (𝕜 := ℂ) (K - P)).le_opNorm ψ
  have hn' : ‖toEuclideanLin K ψ‖ ≤ ‖K - P‖ := by
    simpa only [map_sub, LinearMap.sub_apply, hPψ, sub_zero, hψ, mul_one] using hn
  exact ⟨hinner, pow_le_pow_left₀ (norm_nonneg _) (hn'.trans herr) 2⟩

end Matrix
