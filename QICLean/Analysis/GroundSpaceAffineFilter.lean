/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.HermitianEigenbasisFunctionalCalculus
import QICLean.Analysis.PowerSpectralFilter
import QICLean.Analysis.LowEnergyPerturbation

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
-/

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

end Matrix
