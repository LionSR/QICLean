/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PowerSpectralFilter
import QICLean.Analysis.GroundProjection

/-!
# Spectral powers of a sum of positive contractions

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

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

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
  have hden : 1 - E0 / N = (N - E0) / N := by
    field_simp
  have hbase : (1 - E0 / N)⁻¹ • (1 - N⁻¹ • H) =
      (N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H) := by
    rw [hden, inv_div]
    simp [smul_sub, smul_smul, div_eq_mul_inv, mul_comm, hN.ne']
  have hratio : (1 - (E0 + Δ) / N) / (1 - E0 / N) =
      (N - (E0 + Δ)) / (N - E0) := by
    field_simp
  have hPΩ : toEuclideanLin P Ω = Ω := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, inner_self_eq_norm_sq_to_K, hΩ]
  have hPne : P ≠ 0 := fun hz => by
    simpa [hz, hΩ] using congrArg norm hPΩ
  let K : Matrix ι ι ℂ := ((N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H)) ^ m
  let q : ℝ := (N - (E0 + Δ)) / (N - E0)
  obtain ⟨_, _, _, _, hKpos, hKP, _, herror, _, hKnorm⟩ :=
    hH.power_approximates_isolated_energy_projection h01 hE1N.le hspectrum m
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

end Matrix
