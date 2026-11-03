/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CenteredGroundOperator
import QICLean.Analysis.ProjectedTrialSpaceEnergy
import QICLean.Analysis.RitzGroundSpace

/-!
# Ritz extraction from a space close to the full ground space

The original operator and the candidate space determine the actual compressed
Ritz space. Projecting the full ground space into the candidate constructs
the trial space required by the variational argument. This is the final
spectral extraction in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1641–1643, and proof of `t:alg1`, lines 1814–1817.
-/

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
