/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Projection.ProjectedPositiveEnergy
import QICLean.Analysis.Order.LowEnergyPerturbation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import QICLean.Spectral.Eigenvalue.RitzCompression
import QICLean.Analysis.Subspace.ViableSubspace
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp

/-!
# Ritz extraction from a space close to the full ground space

The original operator and the candidate space determine the actual compressed
Ritz space. Projecting the full ground space into the candidate constructs
the trial space required by the variational argument. This is the final
spectral extraction in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1641–1643, and proof of `t:alg1`, lines 1814–1817.

It also contains the following results.

* `Matrix.IsHermitian.norm_sub_ground_smul_one_le`,
  `Matrix.IsHermitian.sub_ground_smul_one_eq_zero_on_spectralSpanLE`: centering an operator at its
  lowest spectral value.
* `Matrix.IsHermitian.ritzSubspace_isCloseTo_ground_of_trial_energy`: ground-space accuracy of the
  actual Ritz extraction.
-/

section CenteredGroundOperator

/-!
## Centering an operator at its lowest spectral value

The centered Hamiltonian used in the final extraction of ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1814–1817, vanishes on the
full ground space and has norm at most the original norm minus the ground
energy. These spectral facts also apply when the ground space is degenerate.
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Centering at a spectral lower bound gives a positive matrix whose norm is
bounded by the original norm minus that lower bound. This is an auxiliary
spectral estimate for ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1814–1817. -/
theorem IsHermitian.norm_sub_ground_smul_one_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {mu : ℝ}
    (hmu : mu ≤ ‖H‖) (hlow : ∀ z ∈ spectrum ℝ H, mu ≤ z) :
    0 ≤ H - mu • 1 ∧ ‖H - mu • 1‖ ≤ ‖H‖ - mu := by
  have hlo : algebraMap ℝ (Matrix ι ι ℂ) mu ≤ H :=
    (algebraMap_le_iff_le_spectrum hH.isSelfAdjoint).mpr hlow
  have hC0 : 0 ≤ H - mu • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr hlo
  refine ⟨hC0, (CStarAlgebra.norm_le_iff_le_algebraMap _ (sub_nonneg.mpr hmu) hC0).mpr ?_⟩
  simpa only [map_sub, Algebra.algebraMap_eq_smul_one] using
    sub_le_sub_right hH.isSelfAdjoint.le_algebraMap_norm_self
      (algebraMap ℝ (Matrix ι ι ℂ) mu)

/-- The centered operator annihilates the full closed ground-energy span.
The spectral lower bound forces every selected eigenvalue to equal the ground
energy. Auxiliary to ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1814–1817. -/
theorem IsHermitian.sub_ground_smul_one_eq_zero_on_spectralSpanLE
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {mu : ℝ}
    (hlow : ∀ z ∈ spectrum ℝ H, mu ≤ z) :
    ∀ x ∈ Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu,
      toEuclideanCLM (n := ι) (𝕜 := ℂ) (H - mu • 1) x = 0 := by
  have hle : Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu ≤
      (toEuclideanLin (H - mu • 1)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    have heq : hH.eigenvalues j = mu :=
      le_antisymm hj (hlow _ (hH.eigenvalues_mem_spectrum_real j))
    apply WithLp.ofLp_injective 2
    change (H - mu • 1) *ᵥ WithLp.ofLp (hH.eigenvectorBasis j) = 0
    rw [sub_mulVec, smul_mulVec, one_mulVec, hH.mulVec_eigenvectorBasis, heq, sub_self]
  exact fun x hx => hle hx

end Matrix

end CenteredGroundOperator

section RitzGroundSpace

/-!
## Ground-space accuracy of the actual Ritz extraction

A uniform low-energy trial space controls the whole actual compressed Ritz
space. The original spectral gap then bounds its squared projection loss,
and equal dimensions give the same bound in the reverse direction.
This is the variational final step of ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1641–1643, and `t:alg1`, lines 1811–1817.
The trial energy bound is explicit; its construction by physical filtering
and collective trimming is a separate result.
-/

open scoped BigOperators InnerProductSpace

private theorem isCloseTo_low_of_quadraticForm_le
    {E σ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype σ]
    (b : OrthonormalBasis σ ℂ E) (a : σ → ℝ) (H : E →ₗ[ℂ] E)
    (heigen : ∀ j, H (b j) = (a j : ℂ) • b j)
    (mu gamma epsilon : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ j, a j = mu ∨ mu + gamma ≤ a j)
    (R : Submodule ℂ E)
    (hR : ∀ x ∈ R, (inner ℂ x (H x)).re ≤ (mu + epsilon) * ‖x‖ ^ 2) :
    Submodule.IsCloseTo (epsilon / gamma) (Submodule.spectralSpanLE b a mu) R := by
  classical
  let G := Submodule.spectralSpanLE b a mu
  change Submodule.IsCloseTo (epsilon / gamma) G R
  apply Submodule.isCloseTo_iff.mpr
  intro x hx
  have hnorm : ‖x‖ ^ 2 = ∑ j, ‖b.repr x j‖ ^ 2 := by
    simpa only [b.repr_apply_apply] using (b.sum_sq_norm_inner_right x).symm
  have hgapEnergy : gamma * ‖Gᗮ.starProjection x‖ ^ 2 ≤
      (inner ℂ x (H x)).re - mu * ‖x‖ ^ 2 := by
    dsimp only [G]
    rw [Submodule.norm_sq_starProjection_orthogonal_spectralSpanLE,
      Finset.mul_sum, b.re_inner_apply_eq_sum_of_eigen a H heigen, hnorm,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    rcases hgap j with heq | hge
    · simp only [heq, lt_self_iff_false, ite_false, mul_zero, sub_self, le_refl]
    · have hgt : mu < a j := by linarith only [hge, hgamma]
      simp only [hgt, ite_true]
      nlinarith only [mul_le_mul_of_nonneg_right hge (sq_nonneg ‖b.repr x j‖)]
  have hperp : gamma * ‖Gᗮ.starProjection x‖ ^ 2 ≤ epsilon * ‖x‖ ^ 2 := by
    nlinarith only [hgapEnergy, hR x hx]
  have hpy := congrArg (fun t : ℝ ↦ gamma * t)
    (Submodule.norm_sq_eq_add_norm_sq_starProjection x G)
  have hscale : gamma * (1 - epsilon / gamma) = gamma - epsilon := by
    field_simp
  apply _root_.le_of_mul_le_mul_left (a := gamma) ?_ hgamma
  rw [← mul_assoc, hscale]
  nlinarith only [hpy, hperp]

namespace Matrix.IsHermitian

/-- The original Hermitian Hamiltonian and candidate space determine their
actual lowest-dimensional compressed Ritz space before the trial space.
A ground-rank trial space of energy at most mu+epsilon makes that selected
space mutually epsilon/gamma-close to the full original ground space.
This is the variational extraction in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1641–1643, and `t:alg1`, lines 1811–1817.
The trial-space energy estimate is an explicit auxiliary premise. -/
theorem ritzSubspace_isCloseTo_ground_of_trial_energy
    {σ : Type*} [Fintype σ] [DecidableEq σ] {H : Matrix σ σ ℂ}
    (hH : H.IsHermitian) (W : Submodule ℂ (EuclideanSpace ℂ σ))
    (mu gamma epsilon : ℝ) (hgamma : 0 < gamma) (_hmu : mu ∈ spectrum ℝ H)
    (hgap : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) :
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let r := Module.finrank ℂ G
    let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
    ∀ V : Submodule ℂ W, Module.finrank ℂ V = r →
      (∀ x ∈ V, (inner ℂ (H.toEuclideanLin (x : EuclideanSpace ℂ σ))
        (x : EuclideanSpace ℂ σ)).re ≤ (mu + epsilon) * ‖(x : EuclideanSpace ℂ σ)‖ ^ 2) →
      R ≤ W ∧ Module.finrank ℂ R = r ∧
        Submodule.IsCloseTo (epsilon / gamma) G R ∧
        Submodule.IsCloseTo (epsilon / gamma) R G := by
  intro G r R V hdim hV
  let hlinear : H.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hr : r ≤ Module.finrank ℂ W := by
    rw [← hdim]
    exact Submodule.finrank_le V
  have hdimR : Module.finrank ℂ R = r := W.finrank_ritzSubspace hlinear r hr
  have hRle : R ≤ W := W.ritzSubspace_le hlinear r
  have hVright : ∀ x ∈ V,
      (inner ℂ (x : EuclideanSpace ℂ σ) (H.toEuclideanLin (x : EuclideanSpace ℂ σ))).re ≤
        (mu + epsilon) * ‖(x : EuclideanSpace ℂ σ)‖ ^ 2 := by
    intro x hx
    rw [← RCLike.re_to_complex, inner_re_symm, RCLike.re_to_complex]
    exact hV x hx
  have hRenergy : ∀ x ∈ R, (inner ℂ x (H.toEuclideanLin x)).re ≤
      (mu + epsilon) * ‖x‖ ^ 2 := by
    intro x hx
    have hx' : x ∈ W.ritzSubspace hlinear (Module.finrank ℂ V) := by
      simpa only [hdim] using hx
    exact W.re_inner_apply_le_of_mem_ritzSubspace hlinear V (mu + epsilon) hVright hx'
  have heigen (j : σ) : H.toEuclideanLin (hH.eigenvectorBasis j) =
      (hH.eigenvalues j : ℂ) • hH.eigenvectorBasis j :=
    hH.toEuclideanCLM_eigenvectorBasis j
  have hclose : Submodule.IsCloseTo (epsilon / gamma) G R :=
    isCloseTo_low_of_quadraticForm_le hH.eigenvectorBasis hH.eigenvalues
      H.toEuclideanLin heigen mu gamma epsilon hgamma
      (fun j ↦ hgap _ (hH.eigenvalues_mem_spectrum_real j)) R hRenergy
  exact ⟨hRle, hdimR, hclose, hclose.symm_of_finrank_eq hdimR.symm⟩

end Matrix.IsHermitian

end RitzGroundSpace

section RitzGroundSpaceCloseness

open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

/-- A candidate close to the full ground space determines an actual Ritz
space of the ground-space dimension, with a two-sided projection-error bound.
The trial space is constructed by projection. Auxiliary to the final
extraction in ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1814–1817. -/
theorem ritzSubspace_isCloseTo_ground_of_isCloseTo
    {σ : Type*} [Fintype σ] [DecidableEq σ] {H : Matrix σ σ ℂ}
    (hH : H.IsHermitian) (W : Submodule ℂ (EuclideanSpace ℂ σ))
    {mu gamma rho : ℝ} (hgamma : 0 < gamma) (hmu : mu ∈ spectrum ℝ H)
    (hgap : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z)
    (hrho0 : 0 ≤ rho) (hrho : rho < 1)
    (hclose : Submodule.IsCloseTo rho W
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu)) :
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let r := Module.finrank ℂ G
    let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
    let epsilon := (‖H‖ - mu) * rho / (1 - rho) / gamma
    R ≤ W ∧ Module.finrank ℂ R = r ∧
      Submodule.IsCloseTo epsilon G R ∧ Submodule.IsCloseTo epsilon R G := by
  intro G r R epsilon
  have hlow : ∀ z ∈ spectrum ℝ H, mu ≤ z := by
    intro z hz
    rcases hgap z hz with rfl | hge
    · exact le_rfl
    · linarith
  have : Nonempty σ := by
    by_contra hs
    have : IsEmpty σ := not_nonempty_iff.mp hs
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hmu
  have hmuNorm : mu ≤ ‖H‖ :=
    (Real.le_norm_self mu).trans (spectrum.norm_le_norm_of_mem hmu)
  have hCnorm := (hH.norm_sub_ground_smul_one_le hmuNorm hlow).2
  have hCsym : (toEuclideanCLM (n := σ) (𝕜 := ℂ) (H - mu • 1)).toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (hH.sub (isHermitian_one.smul (by simp [IsSelfAdjoint] : IsSelfAdjoint mu)))
  obtain ⟨hVle, hVdim, hVenergy⟩ := hclose.map_starProjection_energy_le hrho0 hrho
    (toEuclideanCLM (n := σ) (𝕜 := ℂ) (H - mu • 1)) hCsym
    (hH.sub_ground_smul_one_eq_zero_on_spectralSpanLE hlow) hCnorm
  let V : Submodule ℂ W := (G.map W.starProjection.toLinearMap).comap W.subtype
  have hmapV : V.map W.subtype = G.map W.starProjection.toLinearMap := by
    exact (Submodule.map_comap_subtype W _).trans (inf_of_le_right hVle)
  have hdim : Module.finrank ℂ V = r := by
    rw [← Submodule.finrank_map_subtype_eq W V, hmapV]
    exact hVdim
  refine hH.ritzSubspace_isCloseTo_ground_of_trial_energy W mu gamma
    ((‖H‖ - mu) * rho / (1 - rho)) hgamma hmu hgap V hdim ?_
  intro x hx
  have hh := hVenergy (x : EuclideanSpace ℂ σ) hx
  have hshift : toEuclideanCLM (n := σ) (𝕜 := ℂ) (H - mu • 1) x =
      H.toEuclideanLin x - mu • (x : EuclideanSpace ℂ σ) := by
    apply WithLp.ofLp_injective 2
    change (H - mu • 1) *ᵥ WithLp.ofLp (x : EuclideanSpace ℂ σ) =
      H *ᵥ WithLp.ofLp (x : EuclideanSpace ℂ σ) -
        mu • WithLp.ofLp (x : EuclideanSpace ℂ σ)
    rw [sub_mulVec, smul_mulVec, one_mulVec]
  rw [hshift, inner_sub_left] at hh
  simp only [inner_smul_left_eq_smul, map_sub, RCLike.smul_re,
    inner_self_eq_norm_sq] at hh
  change (inner ℂ (H.toEuclideanLin (x : EuclideanSpace ℂ σ))
    (x : EuclideanSpace ℂ σ)).re - mu * ‖(x : EuclideanSpace ℂ σ)‖ ^ 2 ≤
      (‖H‖ - mu) * rho / (1 - rho) * ‖(x : EuclideanSpace ℂ σ)‖ ^ 2 at hh
  nlinarith only [hh]

end Matrix.IsHermitian

end RitzGroundSpaceCloseness
