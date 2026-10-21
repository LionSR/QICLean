/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.TraceNormContractivity

/-!
# Power approximation of an isolated ground projection

An affine function of a Hermitian matrix, raised to a natural power,
preserves its isolated ground projection and contracts its complementary
spectral subspace. The estimates retain the exact scalar rate and an explicit
logarithmic threshold for the power. They include zero powers, empty matrix
index types and ground energies of arbitrary multiplicity.

The projection is the complement of the closed excited-energy threshold.
Its norm may vanish; norm one for the power is asserted when the ground
projection is nonzero. Positivity of the scalar function is needed only
on the spectrum.

These are supporting spectral estimates for LVV, arXiv:1307.5143v1,
`algo53.tex`, lines 599–603, equation e:cutdown. The Hamiltonian-specific
spectral hypotheses and the ground-vector specialization are separate.
-/

/-- Quantitative power decay used in LVV, arXiv:1307.5143v1,
equation e:cutdown, line 603. -/
private theorem power_decay_le_of_log_threshold
    {a Δ η : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hΔa : Δ ≤ a)
    (hη : 0 < η) (m : ℕ)
    (hm : a / Δ * Real.log (1 / η) ≤ (m : ℝ)) :
    (1 - Δ / a) ^ m ≤ η := by
  suffices hexp : Real.exp (-(m : ℝ) * Δ / a) ≤ η by
    calc
      (1 - Δ / a) ^ m ≤ Real.exp (-(Δ / a)) ^ m := by
        apply pow_le_pow_left₀ (sub_nonneg.mpr ((div_le_one ha).mpr hΔa))
        exact Real.one_sub_le_exp_neg (Δ / a)
      _ = Real.exp (-(m : ℝ) * Δ / a) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ η := hexp
  apply (Real.le_log_iff_exp_le hη).mp
  have hscaled : a * Real.log (1 / η) ≤ (m : ℝ) * Δ :=
    (div_le_iff₀ hΔ).mp (by simpa only [div_mul_eq_mul_div] using hm)
  rw [one_div, Real.log_inv] at hscaled
  apply (div_le_iff₀ ha).2
  nlinarith

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- Power approximation of an isolated ground-energy projection.
LVV, arXiv:1307.5143v1, lines 599–603, equation e:cutdown.
This is spectral supporting algebra; the physical Hamiltonian hypotheses
are supplied separately by the chain application. -/
theorem IsHermitian.power_approximates_isolated_energy_projection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {E0 E1 M : ℝ} (h01 : E0 < E1) (h1M : E1 ≤ M)
    (hspectrum : ∀ t ∈ spectrum ℝ H,
      t = E0 ∨ t ∈ Set.Icc E1 M) (m : ℕ) :
    let Pg : Matrix ι ι ℂ := 1 - spectralProjectionGE H E1
    let B : Matrix ι ι ℂ := (M - E0)⁻¹ • (M • 1 - H)
    let A : Matrix ι ι ℂ := B ^ m
    let q : ℝ := (M - E1) / (M - E0)
    0 ≤ q ∧ q < 1 ∧ IsStarProjection Pg ∧
      B.PosSemidef ∧ A.PosSemidef ∧
      A * Pg = Pg ∧ Pg * A = Pg ∧
      ‖A - Pg‖ ≤ q ^ m ∧ ‖A‖ ≤ 1 ∧
      (Pg ≠ 0 → ‖A‖ = 1) := by
  let f : ℝ → ℝ := fun t => (M - E0)⁻¹ * (M - t)
  let g : ℝ → ℝ := fun t => if t = E0 then 1 else 0
  have hcont (φ : ℝ → ℝ) : ContinuousOn φ (spectrum ℝ H) :=
    H.finite_real_spectrum.continuousOn φ
  have hB : (M - E0)⁻¹ • (M • (1 : Matrix ι ι ℂ) - H) = cfc f H := by
    simpa only [_root_.cfc_sub (fun _ : ℝ => M) (fun t : ℝ => t) H (hcont _) (hcont _),
      _root_.cfc_const M H hH.isSelfAdjoint, _root_.cfc_id' ℝ H hH.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one] using
      (_root_.cfc_const_mul (M - E0)⁻¹ (fun t : ℝ => M - t) H (hcont _)).symm
  have hA : ((M - E0)⁻¹ • (M • (1 : Matrix ι ι ℂ) - H)) ^ m =
      cfc (fun t => f t ^ m) H := by
    rw [hB, _root_.cfc_pow f m H (hcont _) hH.isSelfAdjoint]
  have hPg : 1 - spectralProjectionGE H E1 = cfc g H := by
    rw [spectralProjectionGE, ← _root_.cfc_one ℝ H hH.isSelfAdjoint,
      ← _root_.cfc_sub _ _ H (hcont _) (hcont _)]
    refine cfc_congr (fun t ht => ?_)
    rcases hspectrum t ht with rfl | hx
    · simp [g, not_le.mpr h01]
    · simp [g, hx.1, ne_of_gt (h01.trans_le hx.1)]
  have hd : 0 < M - E0 := sub_pos.mpr (h01.trans_le h1M)
  have hq0 : 0 ≤ (M - E1) / (M - E0) :=
    div_nonneg (sub_nonneg.mpr h1M) hd.le
  have hq1 : (M - E1) / (M - E0) < 1 :=
    (div_lt_one hd).mpr (sub_lt_sub_left h01 M)
  have hfground : f E0 = 1 := by
    simp [f, hd.ne']
  have hfhigh {t : ℝ} (ht : t ∈ Set.Icc E1 M) :
      0 ≤ f t ∧ f t ≤ (M - E1) / (M - E0) :=
    ⟨mul_nonneg (inv_nonneg.mpr hd.le) (sub_nonneg.mpr ht.2), by
      simpa only [f, div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 M) (inv_nonneg.mpr hd.le)⟩
  have hnormdiff : ‖cfc (fun t => f t ^ m - g t) H‖ ≤
      ((M - E1) / (M - E0)) ^ m := by
    refine norm_cfc_le (pow_nonneg hq0 _) (fun t ht => ?_)
    rcases hspectrum t ht with rfl | hx
    · simpa [hfground, g] using pow_nonneg hq0 m
    · simpa [g, ne_of_gt (h01.trans_le hx.1),
        Real.norm_of_nonneg (pow_nonneg (hfhigh hx).1 m)] using
        pow_le_pow_left₀ (hfhigh hx).1 (hfhigh hx).2 m
  have hf : ∀ t ∈ spectrum ℝ H, 0 ≤ f t ∧ f t ≤ 1 :=
    fun t ht => (hspectrum t ht).elim
      (fun he => he.symm ▸ (show 0 ≤ f E0 ∧ f E0 ≤ 1 from by simp [hfground]))
      (fun hx => ⟨(hfhigh hx).1, (hfhigh hx).2.trans hq1.le⟩)
  have hBpos : (cfc f H).PosSemidef :=
    nonneg_iff_posSemidef.mp (cfc_nonneg fun t ht => (hf t ht).1)
  have hApos : (cfc (fun t => f t ^ m) H).PosSemidef :=
    nonneg_iff_posSemidef.mp (cfc_nonneg fun t ht => pow_nonneg (hf t ht).1 m)
  have hnorm : ‖cfc (fun t => f t ^ m) H‖ ≤ 1 :=
    norm_cfc_le zero_le_one fun t ht => by
      simpa only [Real.norm_of_nonneg (pow_nonneg (hf t ht).1 m)] using
        (pow_le_one₀ (hf t ht).1 (hf t ht).2 : f t ^ m ≤ 1)
  have hfg : (fun t => f t ^ m * g t) = g :=
    funext fun t => by
      by_cases he : t = E0 <;> simp [g, he, hfground]
  have hfix : cfc (fun t => f t ^ m) H * cfc g H = cfc g H :=
    (_root_.cfc_mul (fun t => f t ^ m) g H (hcont _) (hcont _)).symm.trans
      (congrArg (fun φ : ℝ → ℝ => cfc φ H) hfg)
  have hfixrev : cfc g H * cfc (fun t => f t ^ m) H = cfc g H :=
    (cfc_commute_cfc (fun t => f t ^ m) g H).eq.symm.trans hfix
  have hproj : IsStarProjection (cfc g H) :=
    hPg ▸ (hH.isStarProjection_spectralProjectionGE E1).one_sub
  have hdiff : ‖cfc (fun t => f t ^ m) H - cfc g H‖ ≤
      ((M - E1) / (M - E0)) ^ m :=
    (_root_.cfc_sub _ _ H (hcont _) (hcont _)) ▸ hnormdiff
  have hnormeq : cfc g H ≠ 0 → ‖cfc (fun t => f t ^ m) H‖ = 1 :=
    fun hg => le_antisymm hnorm
      (le_of_mul_le_mul_right (by
        simpa only [hfix, one_mul] using
          norm_mul_le (cfc (fun t => f t ^ m) H) (cfc g H)) (norm_pos_iff.mpr hg))
  simp_rw [hA, hB, hPg]
  exact ⟨hq0, hq1, hproj, hBpos, hApos, hfix, hfixrev, hdiff, hnorm, hnormeq⟩

/-- An explicit logarithmic power threshold for the isolated-energy estimate.
LVV, arXiv:1307.5143v1, equation e:cutdown, line 603. -/
theorem IsHermitian.norm_power_sub_projection_le_of_log_threshold
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {E0 E1 M η : ℝ} (h01 : E0 < E1) (h1M : E1 ≤ M)
    (hspectrum : ∀ t ∈ spectrum ℝ H,
      t = E0 ∨ t ∈ Set.Icc E1 M) (hη : 0 < η) (m : ℕ)
    (hm : (M - E0) / (E1 - E0) * Real.log (1 / η) ≤ (m : ℝ)) :
    ‖((M - E0)⁻¹ • (M • (1 : Matrix ι ι ℂ) - H)) ^ m -
      (1 - spectralProjectionGE H E1)‖ ≤ η := by
  obtain ⟨_, _, _, _, _, _, _, herr, _, _⟩ :=
    hH.power_approximates_isolated_energy_projection h01 h1M hspectrum m
  have hd : 0 < M - E0 := sub_pos.mpr (h01.trans_le h1M)
  have hquot : (M - E1) / (M - E0) = 1 - (E1 - E0) / (M - E0) := by
    calc
      (M - E1) / (M - E0) = ((M - E0) - (E1 - E0)) / (M - E0) := by congr 1; ring
      _ = 1 - (E1 - E0) / (M - E0) := by rw [sub_div, div_self hd.ne']
  rw [hquot] at herr
  exact herr.trans (power_decay_le_of_log_threshold hd (sub_pos.mpr h01)
    (sub_le_sub_right h1M E0) hη m hm)

end Matrix
