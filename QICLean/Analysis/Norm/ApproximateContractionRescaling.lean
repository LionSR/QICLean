/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Basic

/-!
# Rescaling an approximate contraction

Let `B` be an element of norm at most one of a complex normed space and `A` an element within
`δ ≥ 0` of `B`, as for an operator approximating a contraction.  Then `‖A‖ ≤ 1 + δ`, the
rescaling `(1 + δ)⁻¹ A` has norm at most one, and it lies within `2δ` of `B`.

## Main results

* `norm_le_one_add_of_norm_sub_le` : `‖A‖ ≤ 1 + δ`.
* `norm_inv_one_add_smul_le_one` : `‖(1 + δ)⁻¹ A‖ ≤ 1`.
* `norm_inv_one_add_smul_sub_le` : `‖(1 + δ)⁻¹ A - B‖ ≤ 2δ`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), reduction to source-only gates,
  `04-compression.tex`, lines 210–212.

Moved from `QICLean.Analysis.TensorProduct.TensorProductContraction`, which was moved from
TNLean, `TNLean/Algebra/TensorProductContraction.lean` at commit `49b78ed821` (Apache-2.0).
-/

section Rescaling

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- An element within `δ` of an element of norm at most one has norm at most `1 + δ`. -/
theorem norm_le_one_add_of_norm_sub_le {A B : E} {δ : ℝ} (hB : ‖B‖ ≤ 1)
    (h : ‖A - B‖ ≤ δ) : ‖A‖ ≤ 1 + δ :=
  calc ‖A‖ = ‖(A - B) + B‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
    _ ≤ 1 + δ := by linarith

/-- Rescaling an element of norm at most `1 + δ` by `(1 + δ)⁻¹` gives norm at most one. -/
theorem norm_inv_one_add_smul_le_one {A : E} {δ : ℝ} (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 1 + δ) :
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • A‖ ≤ 1 := by
  have hpos : 0 < 1 + δ := by linarith
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  calc (1 + δ)⁻¹ * ‖A‖ ≤ (1 + δ)⁻¹ * (1 + δ) := by gcongr
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- Rescaling an element within `δ ≥ 0` of an element of norm at most one by `(1 + δ)⁻¹` gives
an element within `2δ` of it. -/
theorem norm_inv_one_add_smul_sub_le {A B : E} {δ : ℝ} (hδ : 0 ≤ δ) (hB : ‖B‖ ≤ 1)
    (h : ‖A - B‖ ≤ δ) : ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • A - B‖ ≤ 2 * δ := by
  have hA := norm_le_one_add_of_norm_sub_le hB h
  have hpos : 0 < 1 + δ := by linarith
  have hscale : ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • A - A‖ ≤ δ := by
    rw [show (((1 + δ)⁻¹ : ℝ) : ℂ) • A - A = ((((1 + δ)⁻¹ : ℝ) : ℂ) - 1) • A by
      rw [sub_smul, one_smul], norm_smul]
    have hc : ‖(((1 + δ)⁻¹ : ℝ) : ℂ) - 1‖ = δ / (1 + δ) := by
      rw [show (((1 + δ)⁻¹ : ℝ) : ℂ) - 1 = (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
          rw [sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith))]
      field_simp
      ring
    rw [hc]
    calc δ / (1 + δ) * ‖A‖ ≤ δ / (1 + δ) * (1 + δ) := by gcongr
      _ = δ := by field_simp
  calc _ = ‖((((1 + δ)⁻¹ : ℝ) : ℂ) • A - A) + (A - B)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * δ := by linarith

end Rescaling
