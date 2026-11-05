/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CloseSubspaceEnergyTransfer

/-!
# Quantitative regional-energy budgets through a close target

An original-ground regional energy at most two plus a small residual
first transfers to the nearby filter target. A second projection into
the actual powered candidate keeps the energy at most three. The norm
and both losses remain explicit. These are auxiliary estimates for ALVV,
arXiv:1602.08828v2, the energy-estimation argument at line 1807.
-/

namespace Real

/-- A small residual and target-comparison loss retain a regional energy
bound below nine quarters. Scalar auxiliary to ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, line 1807. -/
theorem close_target_positive_energy_le_nine_quarters {A rho tau : ℝ}
    (hA : 0 ≤ A) (hrho : rho ≤ 1 / 16) (htau : 0 ≤ tau)
    (hsmall : tau ≤ 1 / (1024 * (A + 1))) :
    (1 + 1 / (16 : ℝ)) * (2 + rho) + (1 + 16) * A * tau ≤ 9 / 4 := by
  have hmul : tau * (1024 * (A + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 1024 * (A + 1))).mp hsmall
  nlinarith only [hrho, hmul, htau]

/-- The actual projected target remains below regional energy three
when its initial bound is nine quarters. Scalar auxiliary to ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, line 1807. -/
theorem projected_nine_quarters_energy_le_three {A delta : ℝ}
    (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ 1 / (100 * (A + 1))) :
    delta < 1 ∧ (81 / 32 + 9 * A * delta) / (1 - delta) ≤ 3 := by
  have hdelta1 := (projected_positive_energy_le_three hA hdelta hsmall).1
  refine ⟨hdelta1, (div_le_iff₀ (by linarith only [hdelta1] : 0 < 1 - delta)).mpr ?_⟩
  have hmul : delta * (100 * (A + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 100 * (A + 1))).mp hsmall
  nlinarith only [hmul, hdelta]

end Real

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Original regional energy, a close spectral target and a close candidate
give energy at most three on the actual projected target. All norm,
residual and comparison budgets are explicit. Auxiliary to ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, line 1807. -/
theorem IsCloseTo.map_starProjection_energy_le_three_of_close_target
    {rho tau delta A : ℝ} {G T U : Submodule 𝕜 E}
    (hGT : IsCloseTo tau G T) (hUT : IsCloseTo delta U T)
    (H : E →L[𝕜] E) (hH : H.IsPositive)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ (2 + rho) * ‖g‖ ^ 2)
    (hA : ‖H‖ ≤ A) (hrho0 : 0 ≤ rho) (hrho : rho ≤ 1 / 16)
    (htau0 : 0 ≤ tau) (htau : tau ≤ 1 / (1024 * (A + 1)))
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / (100 * (A + 1))) :
    ∀ x ∈ T.map U.starProjection.toLinearMap,
      RCLike.re ⟪H x, x⟫_𝕜 ≤ 3 * ‖x‖ ^ 2 := by
  have hA0 : 0 ≤ A := (norm_nonneg H).trans hA
  have hTraw := hGT.positive_energy_le H hH (by positivity : 0 ≤ 2 + rho) hG hA
    16 (by norm_num)
  have hTnum := Real.close_target_positive_energy_le_nine_quarters hA0 hrho htau0 htau
  have hT : ∀ t ∈ T, RCLike.re ⟪H t, t⟫_𝕜 ≤ (9 / 4 : ℝ) * ‖t‖ ^ 2 :=
    fun t ht ↦ (hTraw t ht).trans (mul_le_mul_of_nonneg_right hTnum (sq_nonneg ‖t‖))
  have hnum := Real.projected_nine_quarters_energy_le_three hA0 hdelta0 hdelta
  have hraw := hUT.map_starProjection_positive_energy_le hdelta0 hnum.1 8
    (by norm_num) H hH (by norm_num) hT hA
  norm_num only at hraw
  exact fun x hx ↦ (hraw x hx).trans
    (mul_le_mul_of_nonneg_right hnum.2 (sq_nonneg ‖x‖))

end Submodule
