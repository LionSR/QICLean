/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftHardTruncation
import QICLean.Analysis.SoftTruncationScaling
import QICLean.Analysis.MatrixBernsteinInputs

/-!
# Exponentially weighted soft-truncation remainders

The scalar exponential remainder estimate gives a uniform bound on its
functional calculus. Factoring through the exponential of the same positive
matrix then controls the remainder on an arbitrary subspace. No exponential
moment is supplied or proved here; a physical application must derive it.

These estimates support corrected independent-scale soft truncations
in ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`,
lines 1178–1255. They do not assert the printed uniform energy estimate.
-/

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

private theorem norm_scalar_weighted_soft_remainder_le (m : ℕ) (hm : 0 < m)
    (t x : ℝ) (ht : 0 < t) (htm : t ≤ 4 * m) (hx : 0 ≤ x) :
    ‖(x - Real.softTruncation t m x) * Real.exp (-x / 8)‖ ≤
      16 * Real.exp (-t / 16) := by
  have hnonneg : 0 ≤ x - Real.softTruncation t m x :=
    sub_nonneg.mpr (Real.softTruncation_bounds t m x ht hm hx).2.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnonneg (Real.exp_nonneg _))]
  have hb := Real.softTruncation_remainder_le_exp_of_scale_le m hm t x ht htm hx
  calc
    _ ≤ (16 * Real.exp (x / 8 - t / 16)) * Real.exp (-x / 8) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = 16 * Real.exp (-t / 16) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem norm_cfc_weighted_soft_remainder_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : 0 < t) (htm : t ≤ 4 * m) :
    ‖cfc (fun x : ℝ ↦ (x - Real.softTruncation t m x) * Real.exp (-x / 8)) A‖ ≤
      16 * Real.exp (-t / 16) := by
  refine norm_cfc_le (by positivity) ?_
  intro x hx
  exact norm_scalar_weighted_soft_remainder_le m hm t x ht htm
    (spectrum_nonneg_of_nonneg hA.nonneg hx)

/-- The weighted remainder times its inverse scalar exponential is the defining soft
remainder of the same matrix. The scale and order are independent. Supporting ALVV,
arXiv:1602.08828v2, `def:ft`, lines 1152–1157. -/
theorem IsHermitian.weighted_softTruncation_remainder_mul_exp
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) (m : ℕ) :
    cfc (fun x : ℝ ↦ (x - Real.softTruncation t m x) * Real.exp (-x / 8)) A *
        NormedSpace.exp ((1 / 8 : ℝ) • A) =
      A - cfc (Real.softTruncation t m) A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  rw [hA.exp_smul_eq_cfc]
  rw [← _root_.cfc_mul _ _ A (hc _) (hc _)]
  have hf : (fun x : ℝ ↦ ((x - Real.softTruncation t m x) *
      Real.exp (-x / 8)) * Real.exp ((1 / 8 : ℝ) * x)) =
      (fun x : ℝ ↦ x - Real.softTruncation t m x) := by
    funext x
    rw [mul_assoc, ← Real.exp_add, show -x / 8 + (1 / 8 : ℝ) * x = 0 by ring,
      Real.exp_zero, mul_one]
  change cfc (fun x : ℝ ↦ ((x - Real.softTruncation t m x) *
    Real.exp (-x / 8)) * Real.exp ((1 / 8 : ℝ) * x)) A = _
  rw [hf, cfc_sub _ _ A (hc _) (hc _), cfc_id' ℝ A hA.isSelfAdjoint]

/-- At an independent positive scale at most four times the order, the actual soft remainder
factors through the exponential of the same positive matrix. Supporting ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx`, lines 1178–1255. This is a matrix-analysis estimate, not
a physical moment or spectral comparison. -/
theorem norm_softTruncation_remainder_domRestrict_le_exp_weight_of_scale_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : 0 < t) (htm : t ≤ 4 * m)
    (G : Submodule ℂ (EuclideanSpace ℂ n)) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
      (A - cfc (Real.softTruncation t m) A)).domRestrict G‖ ≤
      (16 * Real.exp (-t / 16)) *
        ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
          (NormedSpace.exp ((1 / 8 : ℝ) • A))).domRestrict G‖ := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
  let B := cfc (fun x : ℝ ↦
    (x - Real.softTruncation t m x) * Real.exp (-x / 8)) A
  let W := NormedSpace.exp ((1 / 8 : ℝ) • A)
  have hfactor : (T (A - cfc (Real.softTruncation t m) A)).domRestrict G =
      (T B) ∘L (T W).domRestrict G := by
    rw [← hA.isHermitian.weighted_softTruncation_remainder_mul_exp t m, map_mul]
    rfl
  have hB : ‖T B‖ ≤ 16 * Real.exp (-t / 16) := by
    rw [← Matrix.cstar_norm_def]
    exact norm_cfc_weighted_soft_remainder_le A hA m hm t ht htm
  rw [hfactor]
  exact ((T B).opNorm_comp_le ((T W).domRestrict G)).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

/-- The actual soft remainder factors through the exponential of the same
positive matrix. Supporting ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx`, lines 1178–1255. This is a matrix-analysis estimate, not
a physical moment or spectral comparison. -/
theorem norm_softTruncation_remainder_domRestrict_le_exp_weight
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (m : ℕ) (hm : 0 < m)
    (G : Submodule ℂ (EuclideanSpace ℂ n)) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
      (A - cfc (Real.softTruncation (m : ℝ) m) A)).domRestrict G‖ ≤
      (16 * Real.exp (-(m : ℝ) / 16)) *
        ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
          (NormedSpace.exp ((1 / 8 : ℝ) • A))).domRestrict G‖ := by
  exact norm_softTruncation_remainder_domRestrict_le_exp_weight_of_scale_le A hA m hm
    (m : ℝ) (Nat.cast_pos.mpr hm) (by have h := Nat.cast_nonneg (α := ℝ) m; linarith) G

end Matrix
