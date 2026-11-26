/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Real.ChebyshevFilter
import QICLean.Spectral.Projection.ShiftedDensityTruncation
import QICLean.Analysis.TraceNorm.TraceNormContractivity
import QICLean.Spectral.Filter.Gaussian.SpectralGap

/-!
# Hermitian Chebyshev filters and isolated-energy projections

The normalized polynomial gives a Hermitian filter which is at least the
identity on the low-energy compression and contracts the high-energy subspace.
For an isolated energy, the same filter approximates its full spectral projection
without restricting its multiplicity.

**Local fix (positivity):** ALVV's positive-semidefinite spectral-AGSP definition
is not satisfied by every unsquared normalized Chebyshev filter. The statements
here give Hermiticity and the spectral estimates, with the source error recorded
in `docs/paper-gaps/alvv16_chebyshev_filter_positivity.tex`.

Sources: AKLV, arXiv:1301.1162v1, lines 296–325 and 541–583; ALVV,
arXiv:1602.08828v2, the eigenspace, low-energy order and contraction assertions
of Theorem `thm:Cheby-AGSP`, lines 776–843. The near-threshold estimate and
operator Schmidt-rank assertions are separate results.

It also contains the following results.

* `Matrix.IsHermitian.exists_chebyshev_ground_filter`: a Chebyshev filter from a unit ground vector
  and a global gap.
-/

section ChebyshevSpectralFilter

open Polynomial
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A normalized degree-`n` filter is at least the identity on the low-energy
spectral subspace and contracts the high-energy spectral subspace.
AKLV, arXiv:1301.1162v1, lines 541–583; ALVV,
arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, items 1–3.
No positivity of the filter or bound on its operator Schmidt rank is asserted. -/
theorem IsHermitian.exists_polynomial_spectral_filter
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (n : ℕ) {a b u : ℝ}
    (hab : a < b) (hbu : b ≤ u)
    (hupper : ∀ t ∈ spectrum ℝ H, t ≤ u) :
    ∃ p : ℝ[X], p.natDegree = n ∧ p.eval a = 1 ∧
      (∀ t : ℝ, t ≤ a → 1 ≤ p.eval t) ∧
      (∀ t ∈ Set.Icc b u,
        |p.eval t| ≤ 2 * Real.exp
          (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a)))) ∧
      let K : Matrix ι ι ℂ := aeval H p
      let Plo : Matrix ι ι ℂ := cfc (fun t : ℝ ↦ if t ≤ a then 1 else 0) H
      K.IsHermitian ∧ Commute H K ∧
      (Plo * K * Plo - Plo).PosSemidef ∧
      ‖K * spectralProjectionGE H b‖ ≤
        2 * Real.exp (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) := by
  obtain ⟨p, hdegree, hpa, hleft, hbound⟩ :=
    Polynomial.Chebyshev.exists_interval_shrinking_polynomial n hab hbu
  refine ⟨p, hdegree, hpa, hleft, hbound, ?_⟩
  dsimp only
  rw [← cfc_polynomial p H hH.isSelfAdjoint]
  have hhigh : ‖cfc p.eval H * spectralProjectionGE H b‖ ≤
      2 * Real.exp (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) := by
    rw [spectralProjectionGE, ← _root_.cfc_mul p.eval (fun t : ℝ ↦ if b ≤ t then 1 else 0) H
      (H.finite_real_spectrum.continuousOn _) (H.finite_real_spectrum.continuousOn _)]
    apply norm_cfc_le (by positivity)
    intro x hx
    by_cases hbx : b ≤ x
    · simpa only [ite_eq_left hbx, mul_one, Real.norm_eq_abs] using
        hbound x ⟨hbx, hupper x hx⟩
    · simp only [ite_eq_right hbx, mul_zero, norm_zero]
      positivity
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ H) :=
    H.finite_real_spectrum.continuousOn f
  have hlow :
      (cfc (fun t : ℝ ↦ if t ≤ a then 1 else 0) H * cfc p.eval H *
        cfc (fun t : ℝ ↦ if t ≤ a then 1 else 0) H -
          cfc (fun t : ℝ ↦ if t ≤ a then 1 else 0) H).PosSemidef := by
    change cfc (fun t : ℝ ↦ if t ≤ a then 1 else 0) H ≤ _
    rw [← _root_.cfc_mul _ _ H (hcont _) (hcont _),
      ← _root_.cfc_mul _ _ H (hcont _) (hcont _)]
    apply cfc_mono (hf := hcont _) (hg := hcont _)
    intro x hx
    by_cases hxa : x ≤ a
    · simpa only [ite_eq_left hxa, one_mul, mul_one] using hleft x hxa
    · simp only [ite_eq_right hxa, zero_mul, mul_zero, le_refl]
  refine ⟨cfc_predicate p.eval H, ?_, hlow, hhigh⟩
  simpa only [_root_.cfc_id ℝ H hH.isSelfAdjoint] using cfc_commute_cfc id p.eval H

/-- The same filter approximates the spectral projection at an isolated energy,
without restricting the multiplicity of that energy.
AKLV, arXiv:1301.1162v1, lines 296–325 and 541–583;
ALVV, arXiv:1602.08828v2, lines 776–843. -/
theorem IsHermitian.exists_polynomial_approximating_isolated_energy_projection
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (n : ℕ) {a b u : ℝ}
    (hab : a < b) (hbu : b ≤ u)
    (hspectrum : ∀ t ∈ spectrum ℝ H, t = a ∨ t ∈ Set.Icc b u) :
    ∃ p : ℝ[X], p.natDegree = n ∧ p.eval a = 1 ∧
      let K : Matrix ι ι ℂ := aeval H p
      let Pg : Matrix ι ι ℂ := 1 - spectralProjectionGE H b
      IsStarProjection Pg ∧ K * Pg = Pg ∧ Pg * K = Pg ∧
      ‖K - Pg‖ ≤
        2 * Real.exp (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) := by
  have hupper (t : ℝ) (ht : t ∈ spectrum ℝ H) : t ≤ u := by
    rcases hspectrum t ht with rfl | hx
    · exact hab.le.trans hbu
    · exact hx.2
  obtain ⟨p, hdegree, hpa, hleft, hbound, hK⟩ :=
    hH.exists_polynomial_spectral_filter n hab hbu hupper
  refine ⟨p, hdegree, hpa, ?_⟩
  dsimp only at hK ⊢
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ H) :=
    H.finite_real_spectrum.continuousOn f
  have hPg : 1 - spectralProjectionGE H b =
      cfc (fun t : ℝ ↦ if t = a then 1 else 0) H := by
    rw [spectralProjectionGE, ← cfc_one ℝ H hH.isSelfAdjoint,
      ← cfc_sub _ _ H (hcont _) (hcont _)]
    apply cfc_congr
    intro t ht
    rcases hspectrum t ht with rfl | hx
    · simp [not_le.mpr hab]
    · simp [hx.1, ne_of_gt (hab.trans_le hx.1)]
  have hfix : aeval H p * (1 - spectralProjectionGE H b) =
      1 - spectralProjectionGE H b := by
    rw [hPg, ← cfc_polynomial p H hH.isSelfAdjoint,
      ← _root_.cfc_mul _ _ H (hcont _) (hcont _)]
    apply cfc_congr
    intro t ht
    by_cases hta : t = a
    · subst t
      simp [hpa]
    · simp [hta]
  have hcomm : Commute (aeval H p) (1 - spectralProjectionGE H b) := by
    rw [hPg, ← cfc_polynomial p H hH.isSelfAdjoint]
    exact cfc_commute_cfc _ _ H
  have hdiff : aeval H p - (1 - spectralProjectionGE H b) =
      aeval H p * spectralProjectionGE H b := by
    rw [← hfix, mul_sub, mul_one, sub_sub_cancel]
  refine ⟨(hH.isStarProjection_spectralProjectionGE b).one_sub, hfix,
    hcomm.eq.symm.trans hfix, ?_⟩
  rw [hdiff]
  exact hK.2.2.2

end Matrix

end ChebyshevSpectralFilter

section ChebyshevGroundFilter

/-!
## A Chebyshev filter from a unit ground vector and a global gap

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

end ChebyshevGroundFilter
