/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.SpectralExponentialWeights
import QICLean.Analysis.MatrixBernsteinInputs
import QICLean.Analysis.TraceExponentialPerturbation

/-!
# Exponential weights restricted to a spectral subspace

A bound on the high-energy weighted restriction combines with contractivity
on the complementary spectral space. A scalar change of origin then gives
the weight needed for soft truncation. The statements concern arbitrary
finite matrices and subspaces; a physical application must construct the
high-energy restriction rather than supply the desired final moment.

These estimates support ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx`, lines 1178–1255.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

private theorem norm_domRestrict_le {n : Type*} [Fintype n]
    (F : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (G : Submodule ℂ (EuclideanSpace ℂ n)) : ‖F.domRestrict G‖ ≤ ‖F‖ := by
  calc
    ‖F.domRestrict G‖ ≤ ‖F‖ * ‖G.subtypeL‖ := F.opNorm_comp_le G.subtypeL
    _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le G) (norm_nonneg F)
    _ = ‖F‖ := mul_one _

/-- A high-energy weighted restriction and the contractive low-energy part
control the full exponential weight. Supporting ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255. -/
theorem norm_exp_domRestrict_le_of_high_restriction
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (r u s C : ℝ) (hs : 0 ≤ s)
    (G : Submodule ℂ (EuclideanSpace ℂ n)) :
    let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
    let W := NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ)))
    let Q := Matrix.spectralProjectionGE A (r + u)
    ∀ (Z : G →L[ℂ] (T Q).range),
      (T Q).range.subtypeL ∘L Z = (T W * T Q).domRestrict G → ‖Z‖ ≤ C →
      ‖(T W).domRestrict G‖ ≤ 1 + C := by
  intro T W Q Z hZ hZn
  have hhigh : ‖(T W * T Q).domRestrict G‖ = ‖Z‖ := by
    rw [← hZ]
    simpa only [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
      (LinearIsometry.norm_toContinuousLinearMap_comp (T Q).range.subtypeₗᵢ (g := Z))
  have hlow : ‖T W * (1 - T Q)‖ ≤ 1 := by
    calc
      ‖T W * (1 - T Q)‖ = ‖T (W * (1 - Q))‖ := by rw [map_mul, map_sub, map_one]
      _ = ‖W * (1 - Q)‖ := (Matrix.cstar_norm_def _).symm
      _ ≤ 1 := hA.norm_exp_mul_sub_const_mul_lowProjection_le_one s (r + u) hs
  have hsplit : T W = T W * T Q + T W * (1 - T Q) := by noncomm_ring
  rw [hsplit]
  change ‖(T W * T Q).domRestrict G + (T W * (1 - T Q)).domRestrict G‖ ≤ 1 + C
  calc
    _ ≤ ‖(T W * T Q).domRestrict G‖ + ‖(T W * (1 - T Q)).domRestrict G‖ := norm_add_le _ _
    _ ≤ C + 1 := add_le_add (hhigh.le.trans hZn)
      ((norm_domRestrict_le _ G).trans hlow)
    _ = 1 + C := add_comm _ _

/-- Changing the scalar origin of a matrix exponential multiplies its
restriction bound by the corresponding scalar exponential. Supporting ALVV,
arXiv:1602.08828v2, `def:soft-trunc`, lines 1178–1185. -/
theorem norm_shifted_exp_domRestrict_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (r u eps s M : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ n))
    (hM : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
      (NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ))))).domRestrict G‖ ≤ M) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
      (NormedSpace.exp (s • (A - eps • (1 : Matrix n n ℂ))))).domRestrict G‖ ≤
      Real.exp (s * (r + u - eps)) * M := by
  have heq : s • (A - eps • (1 : Matrix n n ℂ)) =
      s • (A - (r + u) • (1 : Matrix n n ℂ)) +
        (s * (r + u - eps)) • (1 : Matrix n n ℂ) := by
    simp only [mul_sub, mul_add, add_smul, sub_smul, smul_sub, smul_add, smul_smul]
    abel
  rw [heq, Matrix.exp_add_smul_one]
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul]
  change ‖Real.exp (s * (r + u - eps)) •
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
      (NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ))))).domRestrict G‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)

end Matrix
