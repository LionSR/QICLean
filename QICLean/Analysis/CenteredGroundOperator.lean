/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyPerturbation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Centering an operator at its lowest spectral value

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
