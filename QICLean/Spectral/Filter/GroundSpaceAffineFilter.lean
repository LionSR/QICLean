/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FunctionalCalculus.TraceCFC
import QICLean.Analysis.Order.LowEnergyPerturbation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QICLean.Spectral.Projection.ShiftedDensityTruncation
import QICLean.Analysis.TraceNorm.TraceNormContractivity

/-!
# The affine filter on the full isolated ground space

The canonical projection of the actual Hermitian matrix is identified with
the orthogonal projection onto its full closed ground-energy span. The
affine normalized filter preserves that entire space, including arbitrary
degeneracy. Its complement contracts with the actual spectral ratio.

These are supporting spectral estimates for ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1620–1643, and the final refinement in the proof
of `t:alg1`, lines 1809–1817. No spatial representation, trimming operation
or algorithmic running time is asserted here.

For a positive matrix, the operator norm is a valid upper end of the spectrum, and the filter
normalized by it has the rate `γ / (‖H‖ - μ)`. That form was moved from TNLean,
`TNLean/MPS/AreaLaw/PhysicalDGFilterTrimming.lean` at commit `49b78ed821` (Apache-2.0).
Changes: stated for an arbitrary positive matrix in place of the Hamiltonian of a chain with
positive terms.

## Main results

* `Matrix.IsHermitian.normalized_affine_ground_filter_spec` — the filter fixes the ground span
  and contracts its complement.
* `Matrix.PosSemidef.normalized_affine_ground_filter_spec_of_norm` — the same with the operator
  norm as upper end of the spectrum.
* `Matrix.IsHermitian.power_approximates_isolated_energy_projection`,
  `Matrix.IsHermitian.norm_power_sub_projection_le_of_log_threshold`: power approximation of an
  isolated ground projection.
-/

section PowerSpectralFilter

/-!
## Power approximation of an isolated ground projection

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

end PowerSpectralFilter

section GroundSpaceAffineFilter

open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

/-- The scalar normalization of the printed affine filter is the same
centered matrix. This is the normalization used in LVV,
arXiv:1307.5143v1, equation `e:cutdown`, lines 599–603, and ALVV,
arXiv:1602.08828v2, final filter, lines 1620–1643. -/
theorem normalized_affine_filter_eq_smul_raw
    {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (mu M : ℝ) (hM : M ≠ 0) :
    (1 - mu / M)⁻¹ • (1 - M⁻¹ • H) =
      (M - mu)⁻¹ • (M • (1 : Matrix ι ι ℂ) - H) := by
  have hden : 1 - mu / M = (M - mu) / M := by
    rw [sub_div, div_self hM]
  rw [hden, inv_div]
  simp [smul_sub, smul_smul, div_eq_mul_inv, mul_comm, hM]

/-- The canonical isolated-ground projection is the orthogonal projection
onto the full original ground-energy span. Auxiliary to ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1817; no rank-one
hypothesis is imposed. -/
theorem IsHermitian.complement_spectralProjectionGE_eq_spectralSpanLE_starProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {mu E1 M : ℝ} (h01 : mu < E1)
    (hspectrum : ∀ z ∈ spectrum ℝ H, z = mu ∨ z ∈ Set.Icc E1 M) :
    toEuclideanLin (1 - spectralProjectionGE H E1) =
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu).starProjection.toLinearMap :=
    by
  classical
  let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
  apply hH.eigenvectorBasis.toBasis.ext
  intro j
  have hspec := hspectrum (hH.eigenvalues j) (hH.eigenvalues_mem_spectrum_real j)
  by_cases hj : hH.eigenvalues j ≤ mu
  · have heq : hH.eigenvalues j = mu := by
      rcases hspec with heq | hx
      · exact heq
      · linarith [hx.1]
    have hG : hH.eigenvectorBasis j ∈ G :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    change toEuclideanLin (1 - spectralProjectionGE H E1) (hH.eigenvectorBasis j) =
      G.starProjection (hH.eigenvectorBasis j)
    rw [Submodule.starProjection_eq_self_iff.mpr hG]
    apply WithLp.ofLp_injective 2
    change (1 - spectralProjectionGE H E1) *ᵥ WithLp.ofLp (hH.eigenvectorBasis j) = _
    rw [sub_mulVec, one_mulVec, spectralProjectionGE, hH.cfc_mulVec_eigenvectorBasis]
    simp only [heq, not_le.mpr h01, ite_false, Complex.ofReal_zero, zero_smul, sub_zero]
  · have hE1 : E1 ≤ hH.eigenvalues j := by
      rcases hspec with heq | hx
      · exact False.elim (hj heq.le)
      · exact hx.1
    have hGo : hH.eigenvectorBasis j ∈ Gᗮ := by
      apply (Submodule.mem_orthogonal' G _).mpr
      intro x hx
      have hc := (Submodule.mem_spectralSpanLE_iff hH.eigenvectorBasis
        hH.eigenvalues mu x).mp hx j (lt_of_not_ge hj)
      simpa only [hH.eigenvectorBasis.repr_apply_apply] using hc
    change toEuclideanLin (1 - spectralProjectionGE H E1) (hH.eigenvectorBasis j) =
      G.starProjection (hH.eigenvectorBasis j)
    rw [(Submodule.starProjection_apply_eq_zero_iff (K := G)).mpr hGo]
    apply WithLp.ofLp_injective 2
    change (1 - spectralProjectionGE H E1) *ᵥ WithLp.ofLp (hH.eigenvectorBasis j) = 0
    rw [sub_mulVec, one_mulVec, spectralProjectionGE, hH.cfc_mulVec_eigenvectorBasis]
    simp only [hE1, ite_true, Complex.ofReal_one, one_smul, sub_self]

/-- The actual affine normalized filter fixes the full isolated ground
space and contracts squared norms on its whole orthogonal complement.
Its scalar rate is the actual spectral ratio. Supporting ALVV,
arXiv:1602.08828v2, final filter in `fig:algo1`, lines 1620–1643,
and the corrected normalized refinement estimate at lines 1809–1817. -/
theorem IsHermitian.normalized_affine_ground_filter_spec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {mu E1 M : ℝ} (h01 : mu < E1) (h1M : E1 ≤ M)
    (hspectrum : ∀ z ∈ spectrum ℝ H, z = mu ∨ z ∈ Set.Icc E1 M) :
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let B : Matrix ι ι ℂ := (M - mu)⁻¹ • (M • 1 - H)
    let K := toEuclideanCLM (n := ι) (𝕜 := ℂ) B
    let c := (E1 - mu) / (M - mu)
    0 < c ∧ c ≤ 1 ∧
      (∀ x ∈ G, K x = x) ∧
      (∀ x ∈ Gᗮ, K x ∈ Gᗮ) ∧
      ∀ x ∈ Gᗮ, ‖K x‖ ^ 2 ≤ (1 - c) * ‖x‖ ^ 2 := by
  intro G B K c
  have hd : 0 < M - mu := sub_pos.mpr (h01.trans_le h1M)
  have hc : 0 < c := div_pos (sub_pos.mpr h01) hd
  have hc1 : c ≤ 1 := (div_le_one hd).mpr (by linarith)
  let P : Matrix ι ι ℂ := 1 - spectralProjectionGE H E1
  have hP := hH.complement_spectralProjectionGE_eq_spectralSpanLE_starProjection h01 hspectrum
  change toEuclideanLin P = G.starProjection.toLinearMap at hP
  obtain ⟨hq0, _hq1, _hproj, _hBpos, _hApos, hBP, hPB, herr, _hnorm, _hnormeq⟩ :=
    hH.power_approximates_isolated_energy_projection h01 h1M hspectrum 1
  simp only [pow_one] at hBP hPB herr
  change B * P = P at hBP
  change P * B = P at hPB
  change ‖B - P‖ ≤ (M - E1) / (M - mu) at herr
  have hrate : (M - E1) / (M - mu) = 1 - c := by
    dsimp only [c]
    field_simp
    ring
  rw [hrate] at herr
  refine ⟨hc, hc1, ?_, ?_, ?_⟩
  · intro x hx
    have hPx : toEuclideanLin P x = x := by
      rw [hP]
      exact Submodule.starProjection_eq_self_iff.mpr hx
    have hh := congrArg (fun A : Matrix ι ι ℂ ↦ toEuclideanLin A x) hBP
    change toEuclideanLin B x = x
    simpa only [toEuclideanLin_mul, LinearMap.comp_apply, hPx] using hh
  · intro x hx
    apply (Submodule.starProjection_apply_eq_zero_iff (K := G)).mp
    have hPx : G.starProjection x = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff (K := G)).mpr hx
    have hh := congrArg (fun A : Matrix ι ι ℂ ↦ toEuclideanLin A x) hPB
    rw [toEuclideanLin_mul, LinearMap.comp_apply, hP] at hh
    change G.starProjection (toEuclideanLin B x) = G.starProjection x at hh
    change G.starProjection (toEuclideanLin B x) = 0
    simpa only [hPx] using hh
  · intro x hx
    have hPx : toEuclideanLin P x = 0 := by
      rw [hP]
      exact (Submodule.starProjection_apply_eq_zero_iff (K := G)).mpr hx
    have hdiff : toEuclideanCLM (n := ι) (𝕜 := ℂ) (B - P) x = K x := by
      change toEuclideanLin (B - P) x = toEuclideanLin B x
      rw [map_sub, LinearMap.sub_apply, hPx, sub_zero]
    have hnorm := (toEuclideanCLM (n := ι) (𝕜 := ℂ) (B - P)).le_opNorm x
    rw [hdiff] at hnorm
    have hbound : ‖K x‖ ≤ (1 - c) * ‖x‖ :=
      hnorm.trans (mul_le_mul_of_nonneg_right herr (norm_nonneg x))
    have hsq : (1 - c) ^ 2 ≤ 1 - c := by nlinarith
    calc
      ‖K x‖ ^ 2 ≤ ((1 - c) * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ ≤ (1 - c) * ‖x‖ ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- **The affine filter normalized by the operator norm.** Let `H ≥ 0` have two eigenvalues
`μ < ν` and no spectrum strictly between `μ` and `μ + γ`, with `γ > 0`. With `M = ‖H‖` and
`c = γ / (M - μ)`, the filter `(M - μ)⁻¹ (M - H)` has `M > 0`, `M - μ > 0`, `0 < c ≤ 1`, fixes
the span `G` of the eigenvectors of energy at most `μ`, preserves `Gᗮ` and contracts squared
norms on `Gᗮ` by `1 - c`. ALVV, arXiv:1602.08828v2, hypothesis (DG), lines 275–279, and the
final filter, lines 1620–1643. -/
theorem PosSemidef.normalized_affine_ground_filter_spec_of_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.PosSemidef) {mu nu gamma : ℝ} (hgamma : 0 < gamma)
    (hmu : mu ∈ spectrum ℝ H) (hnu : nu ∈ spectrum ℝ H) (hmunu : mu < nu)
    (hgap : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) :
    let G := Submodule.spectralSpanLE hH.isHermitian.eigenvectorBasis
      hH.isHermitian.eigenvalues mu
    let M := ‖H‖
    let K := toEuclideanCLM (n := ι) (𝕜 := ℂ) ((M - mu)⁻¹ • (M • 1 - H))
    let c := gamma / (M - mu)
    0 < M ∧ 0 < M - mu ∧ 0 < c ∧ c ≤ 1 ∧
      (∀ x ∈ G, K x = x) ∧
      (∀ x ∈ Gᗮ, K x ∈ Gᗮ) ∧
      ∀ x ∈ Gᗮ, ‖K x‖ ^ 2 ≤ (1 - c) * ‖x‖ ^ 2 := by
  intro G M K c
  have hupper : ∀ z ∈ spectrum ℝ H, z ≤ M :=
    (le_algebraMap_iff_spectrum_le hH.isHermitian.isSelfAdjoint).mp
      (IsSelfAdjoint.le_algebraMap_norm_self H hH.isHermitian.isSelfAdjoint)
  have hE1 : mu + gamma ≤ M := by
    rcases hgap nu hnu with heq | hexc
    · exact False.elim (ne_of_gt hmunu heq)
    · exact hexc.trans (hupper nu hnu)
  have hmu0 : 0 ≤ mu := spectrum_nonneg_of_nonneg hH.nonneg hmu
  have hspec := hH.isHermitian.normalized_affine_ground_filter_spec
    (by linarith : mu < mu + gamma) hE1
    (fun z hz ↦ (hgap z hz).elim Or.inl fun he ↦ Or.inr ⟨he, hupper z hz⟩)
  have hrate : (mu + gamma - mu) / (M - mu) = c := by
    dsimp only [c]
    congr 1
    ring
  rw [hrate] at hspec
  exact ⟨by linarith, by linarith [hupper nu hnu], hspec⟩

end Matrix

end GroundSpaceAffineFilter
