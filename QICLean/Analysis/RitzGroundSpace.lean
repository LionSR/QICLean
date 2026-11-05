/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RitzCompression
import QICLean.Analysis.ViableSubspaceSymmetry
import QICLean.Analysis.EuclideanEigenvectorBasis

/-!
# Ground-space accuracy of the actual Ritz extraction

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
