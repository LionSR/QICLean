/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Comparing vector norms of positive functions of one Hermitian matrix

Pointwise order of two nonnegative spectral functions gives domination of their vector
norms. The proof factors the smaller function through a scalar contraction. This auxiliary
supports comparison of the soft and hard truncations in ALVV, arXiv:1602.08828v2,
Definitions `def:hard-trunc` and `def:soft-trunc`, lines 873–886 and 1178–1185.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- Nonnegative pointwise domination on the spectrum gives domination of vector norms
for two functions of the same Hermitian matrix. This comparison does not require either
function to be operator monotone. Auxiliary to ALVV, arXiv:1602.08828v2,
Definitions `def:hard-trunc` and `def:soft-trunc`, lines 873–886 and 1178–1185. -/
theorem norm_cfc_apply_le_of_nonneg_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (f g : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ A, 0 ≤ f x)
    (hfg : ∀ x ∈ spectrum ℝ A, f x ≤ g x)
    (v : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (cfc f A) v‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (cfc g A) v‖ := by
  let r : ℝ → ℝ := fun x ↦ f x / g x
  have hc (u : ℝ → ℝ) : ContinuousOn u (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn u
  have hr (x : ℝ) (hx : x ∈ spectrum ℝ A) : |r x| ≤ 1 := by
    have hg : 0 ≤ g x := (hf x hx).trans (hfg x hx)
    dsimp only [r]
    rw [abs_of_nonneg (div_nonneg (hf x hx) hg)]
    by_cases hzero : g x = 0
    · simp only [hzero, div_zero, zero_le_one]
    · exact (div_le_one (lt_of_le_of_ne hg (Ne.symm hzero))).mpr (hfg x hx)
  have hfactor : cfc f A = cfc r A * cfc g A := by
    rw [← cfc_mul r g A (hc _) (hc _)]
    apply cfc_congr
    intro x hx
    dsimp only [r]
    by_cases hzero : g x = 0
    · have hfx : f x = 0 := le_antisymm (by simpa only [hzero] using hfg x hx) (hf x hx)
      simp only [hzero, hfx, zero_div, mul_zero]
    · exact (div_mul_cancel₀ (f x) hzero).symm
  have hrnorm : ‖cfc r A‖ ≤ 1 :=
    norm_cfc_le zero_le_one (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hr x hx)
  rw [hfactor, map_mul, mul_apply_eq_comp]
  exact ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (cfc r A)).le_opNorm _).trans
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM, one_mul] using
      mul_le_mul_of_nonneg_right hrnorm (norm_nonneg _))

end Matrix
