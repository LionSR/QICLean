/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.EnergyWeightedPowerDecay
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix order bounds for an energy-weighted contraction power

Continuous functional calculus lifts the scalar energy-weighted estimate to a positive
Hermitian matrix with an isolated zero energy. The upper spectral scale, gap and integer power
threshold remain explicit. This is a conditional operator auxiliary to ALVV,
arXiv:1602.08828v2, `t:alg1`, final power step, lines 1811–1815. The shifted physical
Hamiltonian, its trial space, collective trimming and compressed eigenvectors are separate.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- An isolated zero energy and a sufficient integer power give a two-sided order estimate
for the actual energy-weighted power. Conditional auxiliary to ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1811–1815. The index type may be empty. -/
theorem IsHermitian.energy_weighted_power_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hH0 : 0 ≤ H) {A gamma : ℝ} (hA : 0 < A)
    (hgamma : 0 < gamma) (hgammaA : gamma ≤ A) (hHA : H ≤ A • 1)
    (hspectrum : ∀ s ∈ spectrum ℝ H, s = 0 ∨ gamma ≤ s)
    (tau : ℕ) (hbudget : A ≤ ((tau : ℝ) + 1) * gamma) :
    0 ≤ H * (1 - A⁻¹ • H) ^ (2 * tau) ∧
      H * (1 - A⁻¹ • H) ^ (2 * tau) ≤
        (gamma * (1 - gamma / A) ^ tau) • 1 := by
  let g : ℝ → ℝ := fun s ↦ 1 - A⁻¹ * s
  let f : ℝ → ℝ := fun s ↦ s * g s ^ (2 * tau)
  have hcont (phi : ℝ → ℝ) : ContinuousOn phi (spectrum ℝ H) :=
    H.finite_real_spectrum.continuousOn phi
  have hupper : ∀ s ∈ spectrum ℝ H, s ≤ A :=
    (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hHA)
  have hK : cfc g H = 1 - A⁻¹ • H := by
    rw [_root_.cfc_sub (fun _ : ℝ ↦ 1) (fun s ↦ A⁻¹ * s) H (hcont _) (hcont _),
      _root_.cfc_const (1 : ℝ) H hH.isSelfAdjoint, map_one,
      _root_.cfc_const_mul_id A⁻¹ H hH.isSelfAdjoint]
  have hF : cfc f H = H * (1 - A⁻¹ • H) ^ (2 * tau) := by
    rw [_root_.cfc_mul (fun s : ℝ ↦ s) (fun s ↦ g s ^ (2 * tau)) H (hcont _) (hcont _),
      _root_.cfc_id' ℝ H hH.isSelfAdjoint,
      _root_.cfc_pow g (2 * tau) H (hcont _) hH.isSelfAdjoint, hK]
  have hf0 : ∀ s ∈ spectrum ℝ H, 0 ≤ f s := by
    intro s hs
    exact mul_nonneg (spectrum_nonneg_of_nonneg hH0 hs)
      (pow_nonneg (sub_nonneg.mpr (by
        simpa only [div_eq_mul_inv, mul_comm] using (div_le_one hA).mpr (hupper s hs))) _)
  have hfcap : ∀ s ∈ spectrum ℝ H, f s ≤ gamma * (1 - gamma / A) ^ tau := by
    intro s hs
    rcases hspectrum s hs with rfl | hgs
    · simpa only [f, zero_mul] using mul_nonneg hgamma.le
        (pow_nonneg (sub_nonneg.mpr ((div_le_one hA).mpr hgammaA)) tau)
    · simpa only [f, g, div_eq_mul_inv, mul_comm] using
        Real.energy_mul_one_sub_div_pow_le hA hgamma hgs (hupper s hs) tau hbudget
  constructor
  · rw [← hF]
    exact cfc_nonneg hf0
  · rw [← hF]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      cfc_le_algebraMap f (gamma * (1 - gamma / A) ^ tau) H hfcap (hcont _) hH.isSelfAdjoint

end Matrix
