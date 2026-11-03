/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.HermitianHelpers

/-!
# The spectral characterization of the ground energy

A spectral value below the entire real spectrum of a Hermitian matrix is
its least eigenvalue. No separation from the remaining spectrum is needed.
This elementary finite-dimensional observation supports the energy-estimation
step of ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631.
-/

namespace Matrix.IsHermitian

/-- A spectral lower bound that is itself attained is the least eigenvalue.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631. -/
theorem minEigenvalue_eq_of_mem_spectrum_of_le {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) (mu : ℝ)
    (hmu : mu ∈ spectrum ℝ H) (hlow : ∀ z ∈ spectrum ℝ H, mu ≤ z) :
    minEigenvalue hH = mu := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
    simpa only [hj] using minEigenvalue_le hH j
  · obtain ⟨j, hj⟩ := minEigenvalue_achieved hH
    simpa only [hj] using hlow _ (hH.eigenvalues_mem_spectrum_real j)

end Matrix.IsHermitian
