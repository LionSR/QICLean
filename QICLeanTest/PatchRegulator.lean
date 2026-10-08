/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PatchRegulator

/-! Examples with a noncommuting projection, a singular density, and no indices. -/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace PatchRegulatorTest

private def tiltedProjection : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private def unequalDiagonal : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 4, 0; 0, 1 / 8]

private theorem tiltedProjection_isStarProjection : IsStarProjection tiltedProjection := by
  refine ⟨?_, ?_⟩
  · norm_num [IsIdempotentElem, tiltedProjection, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.ext_iff, Fin.forall_fin_two]
  · change tiltedProjectionᴴ = tiltedProjection
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [tiltedProjection, Matrix.conjTranspose_apply, starRingEnd_apply]

/-- The projection in the trace estimate need not commute with the regulator. -/
example : ¬Commute tiltedProjection unequalDiagonal := by
  intro h
  have h01 := congrFun (congrFun h.eq 0) 1
  norm_num [tiltedProjection, unequalDiagonal, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The trace theorem applies to this explicit noncommuting projection. -/
example {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hTb : unequalDiagonal ≤ (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hTρ : unequalDiagonal ≤ ρ) :
    unequalDiagonal.trace.re ≤ (1 / 4 : ℝ) * tiltedProjection.rank +
      ((1 - tiltedProjection) * ρ).trace.re := by
  exact Matrix.trace_le_smul_rank_add_complement_of_le tiltedProjection_isStarProjection hTb hTρ

/-- A rank-one density may have a zero eigenvalue before the positive shift. -/
example :
    let x : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]
    ((1 / 4 : ℝ) • (x * (x + (1 / 4 : ℝ) • 1)⁻¹)).PosSemidef ∧
      (1 / 4 : ℝ) • (x * (x + (1 / 4 : ℝ) • 1)⁻¹) ≤ (1 / 4 : ℝ) • 1 ∧
      (1 / 4 : ℝ) • (x * (x + (1 / 4 : ℝ) • 1)⁻¹) ≤ x := by
  have hx : (Matrix.diagonal ![0, 1] : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
    norm_num [Matrix.posSemidef_diagonal_iff, Fin.forall_fin_two]
  exact hx.shiftedRegulator_bounds hx (by norm_num) (Commute.refl _)
    (le_add_of_nonneg_right ((Matrix.PosSemidef.one.smul
      (by norm_num : (0 : ℝ) ≤ 1 / 4)).nonneg))

/-- The inverse and order arguments also apply to the empty matrix space. -/
example :
    let x : Matrix (Fin 0) (Fin 0) ℂ := 0
    ((1 : ℝ) • (x * (x + (1 : ℝ) • 1)⁻¹)).PosSemidef ∧
      (1 : ℝ) • (x * (x + (1 : ℝ) • 1)⁻¹) ≤ (1 : ℝ) • 1 ∧
      (1 : ℝ) • (x * (x + (1 : ℝ) • 1)⁻¹) ≤ x := by
  exact (Matrix.PosSemidef.zero (n := Fin 0) (R := ℂ)).shiftedRegulator_bounds
    Matrix.PosSemidef.zero (show (0 : ℝ) < 1 by norm_num) (Commute.refl _)
    (le_add_of_nonneg_right ((Matrix.PosSemidef.one.smul
      (show (0 : ℝ) ≤ 1 by norm_num)).nonneg))

end PatchRegulatorTest
