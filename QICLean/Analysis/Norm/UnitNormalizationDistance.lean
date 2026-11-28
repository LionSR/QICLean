/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Distance after normalization near a unit vector

Normalizing a vector at most doubles its distance to a unit vector:
`‖v / ‖v‖ - ψ‖ ≤ 2 ‖v - ψ‖`, since `|1 - ‖v‖| ≤ ‖v - ψ‖`.

## Main results

* `norm_inv_norm_smul_sub_le_two_mul`: the bound for a nonzero vector, with the scalar
  `(‖Φ‖ : ℂ)⁻¹`.
* `norm_inv_norm_smul_sub_le`: the bound for every vector, with the scalar `((‖v‖⁻¹ : ℝ) : ℂ)`;
  for `v = 0` the normalized vector is zero.

Moved from TNLean, `TNLean/MPS/CanonicalForm/FixedPointApproximation/SecondOrderOverlap.lean` at
commit `021ba0bd19` (Apache-2.0).
-/

/-- Normalizing a nonzero vector at most doubles its distance to a unit vector:
`‖Φ / ‖Φ‖ - ψ‖ ≤ |1 - ‖Φ‖| + ‖Φ - ψ‖ ≤ 2 ‖Φ - ψ‖`. -/
theorem norm_inv_norm_smul_sub_le_two_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ψ Φ : E} (hψ : ‖ψ‖ = 1) (hΦ : Φ ≠ 0) :
    ‖(‖Φ‖ : ℂ)⁻¹ • Φ - ψ‖ ≤ 2 * ‖Φ - ψ‖ := by
  have hpos : 0 < ‖Φ‖ := norm_pos_iff.mpr hΦ
  have hdiff : ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Φ‖ = |1 - ‖Φ‖| := by
    have hs : (‖Φ‖ : ℂ)⁻¹ • Φ - Φ = ((‖Φ‖⁻¹ - 1 : ℝ) : ℂ) • Φ := by
      simp [sub_smul]
    rw [hs, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      ← abs_of_nonneg (norm_nonneg Φ), ← abs_mul]
    congr 1
    rw [abs_of_nonneg (norm_nonneg Φ)]
    field_simp
  have hle : |1 - ‖Φ‖| ≤ ‖Φ - ψ‖ := by
    have h := abs_norm_sub_norm_le ψ Φ
    rwa [hψ, norm_sub_rev] at h
  calc ‖(‖Φ‖ : ℂ)⁻¹ • Φ - ψ‖ ≤ ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Φ‖ + ‖Φ - ψ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖Φ - ψ‖ := by rw [hdiff]; linarith

/-- **Normalization at most doubles the distance.** For any vector `v` and unit vector `ψ`,
`‖v / ‖v‖ - ψ‖ ≤ 2 ‖v - ψ‖`, since `|1 - ‖v‖| ≤ ‖v - ψ‖`. For `v = 0` the left side is
`‖ψ‖ = 1`. -/
theorem norm_inv_norm_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v ψ : E} (hψ : ‖ψ‖ = 1) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ψ‖ ≤ 2 * ‖v - ψ‖ := by
  by_cases hv : v = 0
  · subst hv
    simp [hψ]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h1 : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - v‖ = |1 - ‖v‖| := by
    have e : ((‖v‖⁻¹ : ℝ) : ℂ) • v - v = (((‖v‖⁻¹ - 1 : ℝ)) : ℂ) • v := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← abs_norm v, ← abs_mul, abs_norm,
      sub_mul, inv_mul_cancel₀ hn, one_mul]
  have h2 : |1 - ‖v‖| ≤ ‖v - ψ‖ := by
    rw [← hψ, norm_sub_rev v]
    exact abs_norm_sub_norm_le ψ v
  calc ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ψ‖ = ‖(((‖v‖⁻¹ : ℝ) : ℂ) • v - v) + (v - ψ)‖ := by
        congr 1
        abel
    _ ≤ ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - v‖ + ‖v - ψ‖ := norm_add_le _ _
    _ ≤ 2 * ‖v - ψ‖ := by rw [h1]; linarith

section

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace


/-- For two unit vectors, the deficit of the real inner product is half their
squared distance. This project identity underlies the second-order refinement
of the overlap estimate in arXiv:2307.01696, Supplemental Material, `eq:app_error`. -/
theorem one_sub_re_inner_eq_norm_sub_sq_div_two
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    1 - RCLike.re ⟪x, y⟫_𝕜 = ‖x - y‖ ^ 2 / 2 := by
  have h := @norm_sub_sq 𝕜 E _ _ _ x y
  rw [hx, hy] at h
  linarith

/-- A square matrix of trace one has a nonempty index: `Tr σ = 1` forces `D ≠ 0`. -/
theorem Matrix.neZero_of_trace_eq_one {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (h : σ.trace = 1) : NeZero D :=
  ⟨by rintro rfl; simp at h⟩

end
