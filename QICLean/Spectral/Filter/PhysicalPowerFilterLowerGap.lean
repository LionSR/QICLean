/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Filter.GroundSpaceAffineFilter
import Mathlib.Algebra.Order.Floor.Semiring
import QICLean.Spectral.Filter.Gaussian.SpectralGap

/-!
# Physical spectral powers from a lower bound on the gap

Let H be a finite sum of positive contractions and let Ω be a unit eigenvector
satisfying the rank-one global gap inequality with a positive lower bound Δ.
The normalized powers preserve Ω, have norm one, and approximate its canonical
rank-one projection with error at most exp(-m Δ / (N - E₀)), where N is one
larger than the number of terms. Every positive accuracy has an explicit
logarithmic threshold and a natural-ceiling choice of power.

The local upper bounds give E₀ ≤ N - 1. The proof applies the isolated-energy
power estimate at min(E₀ + Δ, N), while keeping the original Δ in the final
exponential. Thus an excited energy attaining the lower gap is unnecessary,
including when Δ exceeds N - E₀ or the interaction family is empty.

The normalization is the one in LVV, arXiv:1307.5143v1, `algo53.tex`,
lines 599–603, equation e:cutdown. These are auxiliary estimates from a lower
bound on the gap; the attained-first-excitation ratio estimate is developed
separately, in the first section of this module. No locality or spatial
rank estimate is used here.

Every eigenvalue of such a sum lies between 0 and the number of terms. An excited unit vector
orthogonal to Ω gives E₀ + Δ ≤ N - 1, and then the ratio form of e:cutdown holds with the
lower bound Δ in place of an attained first excited energy.

The last two results were moved from TNLean, `TNLean/MPS/AreaLaw/ViableSet/PowerProjector.lean`,
`TNLean/MPS/AreaLaw/ViableSet/SampledProjector.lean` and
`TNLean/MPS/AreaLaw/Huang/PhysicalFilterFamily.lean` at commit `49b78ed821` (Apache-2.0).
Changes: stated for an arbitrary finite family of matrices in place of the bond terms of a
chain, with the number of terms in place of the number of sites less one.

## Main results

* `Matrix.power_filter_exp_spec_of_posSemidef_terms` — the exponential estimate.
* `Matrix.norm_power_filter_sub_ground_le_of_lower_gap_log_threshold` — the logarithmic power.
* `Matrix.eigenvalue_nonneg_and_le_card_of_posSemidef_terms` — `0 ≤ E ≤ |κ|`.
* `Matrix.norm_power_filter_apply_le_ratio_of_lower_gap` — equation e:cutdown.
* `Matrix.power_filter_spec_of_posSemidef_terms`,
  `Matrix.norm_power_filter_sub_ground_le_of_log_threshold`: spectral powers of a sum of positive
  contractions.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

section PhysicalPowerFilter

/-!
## Spectral powers of a sum of positive contractions

Let `H` be a finite sum of positive contractions, with a unit ground vector
satisfying the rank-one global gap inequality. When the excited threshold
is attained, the normalized power in LVV preserves this same ground vector,
has norm one, and contracts its orthogonal complement at the exact scalar rate.

With `N` one larger than the number of terms, the local upper bounds imply
`H ≤ (N - 1) I`. Thus the spectral ceiling and the positivity of the
normalizing denominator follow from the original terms and gap attainment.
No spatial locality is used in these spectral estimates.

Reference: LVV, arXiv:1307.5143v1, `algo53.tex`, lines 209, 283, and 599–603,
equation e:cutdown. For a chain with `N - 1` physical interactions, the extra
unit in `N` corresponds to a zero interaction whose complement is the identity
in the separate ordered-word expansion.
-/

/-- The spectral data and scalar normalization for the positive-contraction power filter.
LVV, arXiv:1307.5143v1, lines 209, 283, and 599–603, equation e:cutdown. -/
private theorem physical_power_filter_spectral_data
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ)
    (hattain : E0 + Δ ∈ spectrum ℝ (∑ i, h i)) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    H.IsHermitian ∧ E0 + Δ ≤ N ∧
      (∀ t ∈ spectrum ℝ H, t = E0 ∨ t ∈ Set.Icc (E0 + Δ) N) ∧
      (1 - spectralProjectionGE H (E0 + Δ) =
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ∧
      ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H) =
        (N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H)) ∧
      ((1 - (E0 + Δ) / N) / (1 - E0 / N) = (N - (E0 + Δ)) / (N - E0)) := by
  let H : Matrix ι ι ℂ := ∑ i, h i
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  have hHpos : H.PosSemidef := posSemidef_sum Finset.univ fun i _ => hpos i
  have hHu : H ≤ (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [H, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using
      (show (∑ i, h i) ≤ ∑ _ : κ, (1 : Matrix ι ι ℂ) from
        Finset.sum_le_sum fun i _ => hupper i)
  have hH : H.IsHermitian := hHpos.isHermitian
  have hbound : ∀ t ∈ spectrum ℝ H, t ≤ (Fintype.card κ : ℝ) :=
    (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hHu)
  have hcardN : (Fintype.card κ : ℝ) < N := by
    simp [N]
  have hE1N : E0 + Δ < N := (hbound _ hattain).trans_lt hcardN
  have h01 : E0 < E0 + Δ := lt_add_of_pos_right E0 hΔ
  have hd : 0 < N - E0 := sub_pos.mpr (h01.trans hE1N)
  have hN : 0 < N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hspectrum : ∀ t ∈ spectrum ℝ H, t = E0 ∨ t ∈ Set.Icc (E0 + Δ) N :=
    fun t ht => by
      obtain ⟨k, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ ht
      exact (GaussianFilter.eigenvector_ground_or_gap hH hΩ hHΩ hgap hΔ k).elim
        (fun hg => Or.inl hg.1)
        (fun he => Or.inr ⟨by linarith [he.1], (hbound _ ht).trans hcardN.le⟩)
  let P : Matrix ι ι ℂ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  have hcanonical : 1 - spectralProjectionGE H (E0 + Δ) = P :=
    hH.complement_spectralProjectionGE_eq_rankOne hΩ hHΩ hgap hΔ
  have hbase := normalized_affine_filter_eq_smul_raw H E0 N hN.ne'
  have hratio : (1 - (E0 + Δ) / N) / (1 - E0 / N) =
      (N - (E0 + Δ)) / (N - E0) := by
    field_simp
  exact ⟨hH, hE1N.le, hspectrum, hcanonical, hbase, hratio⟩

/-- Spectral power approximation from positive contraction terms and an
attained first excited energy. LVV, arXiv:1307.5143v1, lines 209, 283,
and 599–603, equation e:cutdown. No spatial locality is used. -/
theorem power_filter_spec_of_posSemidef_terms
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ)
    (hattain : E0 + Δ ∈ spectrum ℝ (∑ i, h i)) (m : ℕ) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
    let r : ℝ := (1 - (E0 + Δ) / N) / (1 - E0 / N)
    A.PosSemidef ∧ ‖A‖ = 1 ∧ toEuclideanLin A Ω = Ω ∧
      ‖A - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ r ^ m ∧
      ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
        ‖toEuclideanLin A ψ‖ ≤ r ^ m ∧
          ‖⟪ψ, toEuclideanLin A ψ⟫_ℂ‖ ≤ r ^ m := by
  let H : Matrix ι ι ℂ := ∑ i, h i
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  let P : Matrix ι ι ℂ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  have h01 : E0 < E0 + Δ := lt_add_of_pos_right E0 hΔ
  obtain ⟨hH, hE1N, hspectrum, hcanonical, hbase, hratio⟩ :=
    physical_power_filter_spectral_data h hpos hupper hΩ hHΩ hgap hΔ hattain
  change 1 - spectralProjectionGE H (E0 + Δ) = P at hcanonical
  have hPΩ : toEuclideanLin P Ω = Ω := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, inner_self_eq_norm_sq_to_K, hΩ]
  have hPne : P ≠ 0 := fun hz => by
    simpa [hz, hΩ] using congrArg norm hPΩ
  let K : Matrix ι ι ℂ := ((N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H)) ^ m
  let q : ℝ := (N - (E0 + Δ)) / (N - E0)
  obtain ⟨_, _, _, _, hKpos, hKP, _, herror, _, hKnorm⟩ :=
    hH.power_approximates_isolated_energy_projection h01 hE1N hspectrum m
  rw [hcanonical] at hKP herror hKnorm
  have hKΩ : toEuclideanLin K Ω = Ω := by
    simpa only [toEuclideanLin_mul, LinearMap.comp_apply, hPΩ] using
      congrArg (fun T : Matrix ι ι ℂ => toEuclideanLin T Ω) hKP
  dsimp only
  rw [hbase, hratio]
  refine ⟨hKpos, hKnorm hPne, hKΩ, herror, fun ψ hψ horth => ?_⟩
  have hPψ : toEuclideanLin P ψ = 0 := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, horth]
  have hn : ‖toEuclideanLin (K - P) ψ‖ ≤ ‖K - P‖ * ‖ψ‖ :=
    (toEuclideanCLM (n := ι) (𝕜 := ℂ) (K - P)).le_opNorm ψ
  have hn' : ‖toEuclideanLin K ψ‖ ≤ ‖K - P‖ := by
    simpa only [map_sub, LinearMap.sub_apply, hPψ, sub_zero, hψ, mul_one] using hn
  have hvec : ‖toEuclideanLin K ψ‖ ≤ q ^ m := hn'.trans herror
  have hinner : ‖⟪ψ, toEuclideanLin K ψ⟫_ℂ‖ ≤ ‖toEuclideanLin K ψ‖ := by
    simpa only [hψ, one_mul] using norm_inner_le_norm ψ (toEuclideanLin K ψ)
  exact ⟨hvec, hinner.trans hvec⟩

/-- An explicit logarithmic accuracy threshold for the physical power filter.
LVV, arXiv:1307.5143v1, lines 599–603, equation e:cutdown.
The threshold is an attained first excited energy, as in lines 209 and 283. -/
theorem norm_power_filter_sub_ground_le_of_log_threshold
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ)
    (hattain : E0 + Δ ∈ spectrum ℝ (∑ i, h i))
    {η : ℝ} (hη : 0 < η) (m : ℕ)
    (hm : ((((Fintype.card κ + 1 : ℕ) : ℝ) - E0) / Δ) *
      Real.log (1 / η) ≤ (m : ℝ)) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
    ‖A - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ η := by
  let H : Matrix ι ι ℂ := ∑ i, h i
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  obtain ⟨hH, hE1N, hspectrum, hcanonical, hbase, _⟩ :=
    physical_power_filter_spectral_data h hpos hupper hΩ hHΩ hgap hΔ hattain
  have hm' : (N - E0) / ((E0 + Δ) - E0) * Real.log (1 / η) ≤ (m : ℝ) := by
    simpa only [add_sub_cancel_left] using hm
  have herr := hH.norm_power_sub_projection_le_of_log_threshold
    (lt_add_of_pos_right E0 hΔ) hE1N hspectrum hη m hm'
  simpa only [← hbase, hcanonical] using herr

end PhysicalPowerFilter

section PhysicalPowerFilterLowerGap

/-- Evaluation of an operator upper bound on the given unit eigenvector.
This supplies the denominator bound without an excited-energy witness. -/
private theorem eigenvalue_le_scalar_of_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} {c E0 : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hu : H ≤ c • (1 : Matrix ι ι ℂ))
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω) :
    E0 ≤ c := by
  classical
  have hn : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = (1 : ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  have hq := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp hu).dotProduct_mulVec_nonneg (WithLp.ofLp Ω))).1
  rw [sub_mulVec, smul_mulVec, one_mulVec, hHΩ, dotProduct_sub] at hq
  simp only [dotProduct_smul, hn] at hq
  have hce : 0 ≤ c - E0 := by
    simpa only [Complex.real_smul, smul_eq_mul, mul_one,
      Complex.sub_re, Complex.ofReal_re] using hq
  exact sub_nonneg.mp hce

/-- The physical normalized power approximates the canonical ground projection
using only the positive lower gap bound. Supporting extension of LVV,
arXiv:1307.5143v1, `algo53.tex:599–603`, equation `e:cutdown`. -/
theorem power_filter_exp_spec_of_posSemidef_terms
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) (m : ℕ) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
    let err : ℝ := Real.exp (-(m : ℝ) * Δ / (N - E0))
    A.PosSemidef ∧ ‖A‖ = 1 ∧ toEuclideanLin A Ω = Ω ∧
      ‖A - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ err ∧
      ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
        ‖toEuclideanLin A ψ‖ ≤ err ∧
          ‖⟪ψ, toEuclideanLin A ψ⟫_ℂ‖ ≤ err := by
  classical
  let H : Matrix ι ι ℂ := ∑ i, h i
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  let P : Matrix ι ι ℂ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  have hHpos : H.PosSemidef := posSemidef_sum Finset.univ fun i _ => hpos i
  have hHu : H ≤ (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [H, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using
      (show (∑ i, h i) ≤ ∑ _ : κ, (1 : Matrix ι ι ℂ) from
        Finset.sum_le_sum fun i _ => hupper i)
  have hH : H.IsHermitian := hHpos.isHermitian
  have hE0c : E0 ≤ (Fintype.card κ : ℝ) :=
    eigenvalue_le_scalar_of_upper hHu hΩ hHΩ
  have hcardN : (Fintype.card κ : ℝ) < N := by simp [N]
  have hE0N : E0 < N := hE0c.trans_lt hcardN
  have ha : 0 < N - E0 := sub_pos.mpr hE0N
  have hN : 0 < N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hbound : ∀ t ∈ spectrum ℝ H, t ≤ (Fintype.card κ : ℝ) :=
    (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hHu)
  have hspectrum : ∀ t ∈ spectrum ℝ H,
      t = E0 ∨ t ∈ Set.Icc (E0 + Δ) N := by
    intro t ht
    obtain ⟨k, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ ht
    exact (GaussianFilter.eigenvector_ground_or_gap hH hΩ hHΩ hgap hΔ k).elim
      (fun hg => Or.inl hg.1)
      (fun he => Or.inr ⟨by linarith [he.1], (hbound _ ht).trans hcardN.le⟩)
  let EStar : ℝ := min (E0 + Δ) N
  have h0Star : E0 < EStar :=
    lt_min (lt_add_of_pos_right E0 hΔ) hE0N
  have hStarN : EStar ≤ N := min_le_right _ _
  have hclipSpectrum : ∀ t ∈ spectrum ℝ H,
      t = E0 ∨ t ∈ Set.Icc EStar N := by
    intro t ht
    exact (hspectrum t ht).elim Or.inl
      (fun hx => Or.inr ⟨(min_le_left _ _).trans hx.1, hx.2⟩)
  have hsame : spectralProjectionGE H EStar =
      spectralProjectionGE H (E0 + Δ) := by
    unfold spectralProjectionGE
    refine cfc_congr (fun t ht => ?_)
    rcases hspectrum t ht with hg | hx
    · simp only [hg, not_le.mpr h0Star,
        not_le.mpr (lt_add_of_pos_right E0 hΔ), ite_false]
    · simp only [show EStar ≤ t from (min_le_left (E0 + Δ) N).trans hx.1,
        hx.1, ite_true]
  have hcanonical : 1 - spectralProjectionGE H EStar = P := by
    rw [hsame]
    exact hH.complement_spectralProjectionGE_eq_rankOne hΩ hHΩ hgap hΔ
  let K : Matrix ι ι ℂ := ((N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H)) ^ m
  let qStar : ℝ := (N - EStar) / (N - E0)
  obtain ⟨hq0, _, _, _, hKpos, hKP, _, herror, _, hKnorm⟩ :=
    hH.power_approximates_isolated_energy_projection
      (E0 := E0) (E1 := EStar) (M := N) h0Star hStarN hclipSpectrum m
  rw [hcanonical] at hKP herror hKnorm
  change 0 ≤ qStar at hq0
  change K.PosSemidef at hKpos
  change K * P = P at hKP
  change ‖K - P‖ ≤ qStar ^ m at herror
  change P ≠ 0 → ‖K‖ = 1 at hKnorm
  have hqexp : qStar ≤ Real.exp (-(Δ / (N - E0))) := by
    by_cases hlow : E0 + Δ ≤ N
    · have hquot : qStar = 1 - Δ / (N - E0) := by
        dsimp only [qStar, EStar]
        rw [min_eq_left hlow]
        calc
          (N - (E0 + Δ)) / (N - E0) =
              ((N - E0) - Δ) / (N - E0) := by congr 1; ring
          _ = 1 - Δ / (N - E0) := by rw [sub_div, div_self ha.ne']
      rw [hquot]
      exact Real.one_sub_le_exp_neg (Δ / (N - E0))
    · have hhigh : N ≤ E0 + Δ := le_of_lt (lt_of_not_ge hlow)
      have hzero : qStar = 0 := by simp [qStar, EStar, min_eq_right hhigh]
      rw [hzero]
      exact (Real.exp_pos _).le
  have hrate : qStar ^ m ≤ Real.exp (-(m : ℝ) * Δ / (N - E0)) := by
    calc
      qStar ^ m ≤ Real.exp (-(Δ / (N - E0))) ^ m :=
        pow_le_pow_left₀ hq0 hqexp m
      _ = Real.exp (-(m : ℝ) * Δ / (N - E0)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have herrExp : ‖K - P‖ ≤ Real.exp (-(m : ℝ) * Δ / (N - E0)) :=
    herror.trans hrate
  have hbase := normalized_affine_filter_eq_smul_raw H E0 N hN.ne'
  have hPΩ : toEuclideanLin P Ω = Ω := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply,
      inner_self_eq_norm_sq_to_K, hΩ]
  have hPne : P ≠ 0 := fun hz => by
    simpa [hz, hΩ] using congrArg norm hPΩ
  have hKΩ : toEuclideanLin K Ω = Ω := by
    simpa only [toEuclideanLin_mul, LinearMap.comp_apply, hPΩ] using
      congrArg (fun T : Matrix ι ι ℂ => toEuclideanLin T Ω) hKP
  dsimp only
  rw [hbase]
  refine ⟨hKpos, hKnorm hPne, hKΩ, herrExp, fun ψ hψ horth => ?_⟩
  have hPψ : toEuclideanLin P ψ = 0 := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, horth]
  have hn : ‖toEuclideanLin (K - P) ψ‖ ≤ ‖K - P‖ * ‖ψ‖ :=
    (toEuclideanCLM (n := ι) (𝕜 := ℂ) (K - P)).le_opNorm ψ
  have hn' : ‖toEuclideanLin K ψ‖ ≤ ‖K - P‖ := by
    simpa only [map_sub, LinearMap.sub_apply, hPψ, sub_zero, hψ, mul_one] using hn
  have hvec : ‖toEuclideanLin K ψ‖ ≤ Real.exp (-(m : ℝ) * Δ / (N - E0)) :=
    hn'.trans herrExp
  have hinner : ‖⟪ψ, toEuclideanLin K ψ⟫_ℂ‖ ≤ ‖toEuclideanLin K ψ‖ := by
    simpa only [hψ, one_mul] using norm_inner_le_norm ψ (toEuclideanLin K ψ)
  exact ⟨hvec, hinner.trans hvec⟩

/-- Exact logarithmic threshold for the same physical power and original lower
gap. No assumption that the target error is below one is required. -/
theorem norm_power_filter_sub_ground_le_of_lower_gap_log_threshold
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) {η : ℝ} (hη : 0 < η) (m : ℕ)
    (hm : ((((Fintype.card κ + 1 : ℕ) : ℝ) - E0) / Δ) *
      Real.log (1 / η) ≤ (m : ℝ)) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
    ‖A - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ η := by
  classical
  let H : Matrix ι ι ℂ := ∑ i, h i
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  let P : Matrix ι ι ℂ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
  have hHu : H ≤ (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [H, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using
      (show (∑ i, h i) ≤ ∑ _ : κ, (1 : Matrix ι ι ℂ) from
        Finset.sum_le_sum fun i _ => hupper i)
  have hE0c : E0 ≤ (Fintype.card κ : ℝ) :=
    eigenvalue_le_scalar_of_upper hHu hΩ hHΩ
  have hcardN : (Fintype.card κ : ℝ) < N := by simp [N]
  have ha : 0 < N - E0 := sub_pos.mpr (hE0c.trans_lt hcardN)
  obtain ⟨_, _, _, herr, _⟩ :=
    power_filter_exp_spec_of_posSemidef_terms h hpos hupper hΩ hHΩ hgap hΔ m
  change ‖A - P‖ ≤ Real.exp (-(m : ℝ) * Δ / (N - E0)) at herr
  change (N - E0) / Δ * Real.log (1 / η) ≤ (m : ℝ) at hm
  have hexp : Real.exp (-(m : ℝ) * Δ / (N - E0)) ≤ η := by
    apply (Real.le_log_iff_exp_le hη).mp
    have hscaled : (N - E0) * Real.log (1 / η) ≤ (m : ℝ) * Δ :=
      (div_le_iff₀ hΔ).mp (by simpa only [div_mul_eq_mul_div] using hm)
    rw [one_div, Real.log_inv] at hscaled
    apply (div_le_iff₀ ha).2
    nlinarith
  exact herr.trans hexp

/-- A concrete natural power achieving every positive requested error.
The natural ceiling already truncates a negative threshold to zero. -/
theorem norm_power_filter_sub_ground_le_at_lower_gap_ceil
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) {η : ℝ} (hη : 0 < η) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    let m : ℕ := Nat.ceil (((N - E0) / Δ) * Real.log (1 / η))
    let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
    ‖A - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ η := by
  classical
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  let m : ℕ := Nat.ceil (((N - E0) / Δ) * Real.log (1 / η))
  exact norm_power_filter_sub_ground_le_of_lower_gap_log_threshold
    h hpos hupper hΩ hHΩ hgap hΔ hη m (Nat.le_ceil _)

/-- **Eigenvalues of a sum of positive contractions.** If `H = ∑ᵢ hᵢ` is a finite sum of
matrices with `0 ≤ hᵢ ≤ 1` and `H Ω = E Ω` for a unit vector `Ω`, then `0 ≤ E ≤ |κ|`, the
number of terms. LVV, arXiv:1307.5143v1, `algo53.tex`, lines 283–284 and 607, where this
makes the normalization `(1 - ε₀/n)⁻¹` of the power filter well defined. -/
theorem eigenvalue_nonneg_and_le_card_of_posSemidef_terms
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ) (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E : ℝ} {Ω : EuclideanSpace ℂ ι} (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E : ℂ) • WithLp.ofLp Ω) :
    0 ≤ E ∧ E ≤ Fintype.card κ := by
  have hHu : (∑ i, h i) ≤ (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using
      (show (∑ i, h i) ≤ ∑ _ : κ, (1 : Matrix ι ι ℂ) from
        Finset.sum_le_sum fun i _ => hupper i)
  refine ⟨?_, eigenvalue_le_scalar_of_upper hHu hΩ hHΩ⟩
  have hneg : -(∑ i, h i) ≤ (0 : ℝ) • (1 : Matrix ι ι ℂ) := by
    rw [zero_smul, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => (hpos i).nonneg
  have hnegΩ : -(∑ i, h i) *ᵥ WithLp.ofLp Ω = ((-E : ℝ) : ℂ) • WithLp.ofLp Ω := by
    rw [neg_mulVec, hHΩ, Complex.ofReal_neg, neg_smul]
  linarith [eigenvalue_le_scalar_of_upper hneg hΩ hnegΩ]

/-- **Equation `e:cutdown` from a lower bound on the gap.** Let `H = ∑ᵢ hᵢ` be a finite sum
of matrices with `0 ≤ hᵢ ≤ 1`, `N` one more than the number of terms, `Ω` a unit vector with
`H Ω = E₀ Ω`, and `H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)` with `Δ > 0`. For every unit vector `ψ`
orthogonal to `Ω`, the normalized power `A = ((1 - H/N) / (1 - E₀/N))^m` satisfies
`‖A ψ‖ ≤ r^m` and `|⟨ψ, A ψ⟩| ≤ r^m` with `r = (1 - (E₀ + Δ)/N) / (1 - E₀/N)`. The energy
`E₀ + Δ` need not be attained: `Δ` is any positive lower bound on the gap. LVV,
arXiv:1307.5143v1, `algo53.tex`, line 603. -/
theorem norm_power_filter_apply_le_ratio_of_lower_gap
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) (m : ℕ) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (horth : ⟪Ω, ψ⟫_ℂ = 0) :
    let H := ∑ i, h i
    let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
    let A : Matrix ι ι ℂ := ((1 - E0 / N)⁻¹ • (1 - N⁻¹ • H)) ^ m
    let r : ℝ := (1 - (E0 + Δ) / N) / (1 - E0 / N)
    ‖toEuclideanLin A ψ‖ ≤ r ^ m ∧ ‖⟪ψ, toEuclideanLin A ψ⟫_ℂ‖ ≤ r ^ m := by
  classical
  let H : Matrix ι ι ℂ := ∑ i, h i
  let N : ℝ := ((Fintype.card κ + 1 : ℕ) : ℝ)
  let P : Matrix ι ι ℂ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  have hH : H.IsHermitian := (posSemidef_sum Finset.univ fun i _ => hpos i).isHermitian
  have hHu : H ≤ (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [H, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using
      (show (∑ i, h i) ≤ ∑ _ : κ, (1 : Matrix ι ι ℂ) from
        Finset.sum_le_sum fun i _ => hupper i)
  have hcardN : (Fintype.card κ : ℝ) < N := by simp [N]
  have hN : 0 < N := Nat.cast_pos.mpr (Nat.succ_pos _)
  -- The excited vector `ψ` gives `E₀ + Δ ≤ |κ|`.
  have hexc : E0 + Δ ≤ (Fintype.card κ : ℝ) := by
    have hlow := PosSemidef.gap_le (H := H) hgap ψ
    rw [hψ, horth, norm_zero] at hlow
    have hup := (isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hHu)).re_inner_nonneg_right ψ
    rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub] at hup
    have hc : RCLike.re ⟪ψ, toEuclideanLin ((Fintype.card κ : ℝ) •
        (1 : Matrix ι ι ℂ)) ψ⟫_ℂ = (Fintype.card κ : ℝ) := by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, inner_smul_right]
      simp [inner_self_eq_norm_sq_to_K, hψ]
    rw [hc, RCLike.re_to_complex] at hup
    linarith
  have hE0N : E0 < N := by linarith
  have ha : 0 < N - E0 := sub_pos.mpr hE0N
  have hbound : ∀ t ∈ spectrum ℝ H, t ≤ (Fintype.card κ : ℝ) :=
    (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hHu)
  have hspectrum : ∀ t ∈ spectrum ℝ H, t = E0 ∨ t ∈ Set.Icc (E0 + Δ) N := by
    intro t ht
    obtain ⟨k, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ ht
    exact (GaussianFilter.eigenvector_ground_or_gap hH hΩ hHΩ hgap hΔ k).elim
      (fun hg => Or.inl hg.1)
      (fun he => Or.inr ⟨by linarith [he.1], (hbound _ ht).trans hcardN.le⟩)
  obtain ⟨-, -, -, -, -, -, -, herror, -, -⟩ :=
    hH.power_approximates_isolated_energy_projection (lt_add_of_pos_right E0 hΔ)
      (hexc.trans hcardN.le) hspectrum m
  rw [hH.complement_spectralProjectionGE_eq_rankOne hΩ hHΩ hgap hΔ] at herror
  have hratio : (1 - (E0 + Δ) / N) / (1 - E0 / N) = (N - (E0 + Δ)) / (N - E0) := by
    rw [one_sub_div hN.ne', one_sub_div hN.ne', div_div_div_cancel_right₀ hN.ne']
  dsimp only
  rw [normalized_affine_filter_eq_smul_raw H E0 N hN.ne', hratio]
  set K := ((N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H)) ^ m
  have hPψ : toEuclideanLin P ψ = 0 := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, horth]
  have hn : ‖toEuclideanLin (K - P) ψ‖ ≤ ‖K - P‖ * ‖ψ‖ :=
    (toEuclideanCLM (n := ι) (𝕜 := ℂ) (K - P)).le_opNorm ψ
  have hvec : ‖toEuclideanLin K ψ‖ ≤ ((N - (E0 + Δ)) / (N - E0)) ^ m := by
    refine le_trans ?_ herror
    simpa only [map_sub, LinearMap.sub_apply, hPψ, sub_zero, hψ, mul_one] using hn
  have hinner : ‖⟪ψ, toEuclideanLin K ψ⟫_ℂ‖ ≤ ‖toEuclideanLin K ψ‖ := by
    simpa only [hψ, one_mul] using norm_inner_le_norm ψ (toEuclideanLin K ψ)
  exact ⟨hvec, hinner.trans hvec⟩

end PhysicalPowerFilterLowerGap

end Matrix
