/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RestoringCoefficientBound

/-! Singular, noncommuting consumers with an unrestricted row sum. -/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace RestoringCoefficientBoundTest

private def weight : Fin 3 → ℝ := ![2, 3, 0]

private def reference : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal fun x ↦ (weight x : ℂ)

private def small : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec ![1, 1, 0] (star ![1, 1, 0])

private theorem reference_posSemidef : reference.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [weight]

private theorem small_posSemidef : small.PosSemidef :=
  posSemidef_vecMulVec_self_star _

private theorem small_le_reference : small ≤ reference := by
  have hdiff : reference - small =
      vecMulVec ![1, -1, 0] (star ![1, -1, 0]) + diagonal ![0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [reference, weight, small, vecMulVec, diagonal]
  apply Matrix.le_iff.mpr
  rw [hdiff]
  exact (posSemidef_vecMulVec_self_star _).add
    (PosSemidef.diagonal (show ∀ i : Fin 3, 0 ≤ (![0, 1, 0] : Fin 3 → ℂ) i by
      intro i
      fin_cases i <;> norm_num))

-- The zero diagonal coordinate is allowed, and the support inverse retains it.
example : reference_posSemidef.supportInv =
    diagonal ![(1 / 2 : ℂ), 1 / 3, 0] := by
  rw [reference_posSemidef.supportInv_eq_diagonal (p := weight) rfl]
  congr 1
  funext i
  fin_cases i <;> norm_num [weight]

example : 0 ≤ weight 2 ∧ weight 2 = 0 :=
  ⟨reference_posSemidef.nonneg_of_eq_diagonal (p := weight) rfl 2, rfl⟩

-- These matrices do not commute, and the reference has a nonzero kernel vector.
example : small * reference ≠ reference * small ∧
    (![0, 0, 1] : Fin 3 → ℂ) ≠ 0 ∧ reference *ᵥ ![0, 0, 1] = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 0 1) h
    norm_num [reference, weight, small, Matrix.mul_apply, Fin.sum_univ_succ,
      vecMulVec, diagonal] at this
  · intro h
    have := congrArg (fun v : Fin 3 → ℂ ↦ v 2) h
    norm_num at this
  · ext i
    fin_cases i <;>
      norm_num [reference, weight, mulVec, dotProduct, Fin.sum_univ_succ, diagonal]

-- Selecting only column 0 still includes row 1, which contributes a nonzero term.
example : (∑ x ∈ ({0} : Finset (Fin 3)), ∑ y : Fin 3,
      ‖small y x‖ ^ 2 / weight x) = 1 ∧
    (∑ x ∈ ({0} : Finset (Fin 3)), ∑ y ∈ ({0} : Finset (Fin 3)),
      ‖small y x‖ ^ 2 / weight x) = 1 / 2 := by
  norm_num [small, weight, vecMulVec, Fin.sum_univ_succ]

example : (trace (small * reference_posSemidef.supportInv * small)).re =
    ∑ x : Fin 3, ∑ y : Fin 3, ‖small y x‖ ^ 2 / weight x :=
  small_posSemidef.trace_mul_supportInv_mul_re reference_posSemidef rfl

example : (∑ x ∈ ({0} : Finset (Fin 3)), ∑ y : Fin 3,
      ‖small y x‖ ^ 2 / weight x) ≤
        (trace (small * reference_posSemidef.supportInv * small)).re ∧
    (trace (small * reference_posSemidef.supportInv * small)).re ≤ (trace small).re :=
  small_posSemidef.selected_sum_sq_div_le_trace reference_posSemidef rfl
    small_le_reference {0}

-- The selected zero coordinate adds zero without deleting it from the ambient basis.
example : (∑ x ∈ ({0, 2} : Finset (Fin 3)), ∑ y : Fin 3,
      ‖small y x‖ ^ 2 / weight x) ≤
    (trace (small * reference_posSemidef.supportInv * small)).re :=
  small_posSemidef.selected_sum_sq_div_le_trace_mul_supportInv_mul
    reference_posSemidef rfl {0, 2}

end RestoringCoefficientBoundTest
