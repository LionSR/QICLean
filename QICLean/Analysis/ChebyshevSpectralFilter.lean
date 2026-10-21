/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevFilter
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.TraceNormContractivity

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
-/

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
