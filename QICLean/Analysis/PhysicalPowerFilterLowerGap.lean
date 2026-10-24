/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PhysicalPowerFilter
import Mathlib.Algebra.Order.Floor.Semiring

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
separately in `QICLean.Analysis.PhysicalPowerFilter`. No locality or spatial
rank estimate is used here.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

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
  have hden : 1 - E0 / N = (N - E0) / N := by
    rw [sub_div, div_self hN.ne']
  have hbase : (1 - E0 / N)⁻¹ • (1 - N⁻¹ • H) =
      (N - E0)⁻¹ • (N • (1 : Matrix ι ι ℂ) - H) := by
    rw [hden, inv_div]
    simp [smul_sub, smul_smul, div_eq_mul_inv, mul_comm, hN.ne']
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


end Matrix
