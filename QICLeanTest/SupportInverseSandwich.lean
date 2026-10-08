/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SupportInverseSandwich

/-! Singular and noncommuting consumers of the support-inverse order bound. -/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SupportInverseSandwichTest

private def small : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec ![1, 1, 0] (star ![1, 1, 0])

private def reference : Matrix (Fin 3) (Fin 3) ℂ :=
  small + diagonal ![1, 2, 0]

private theorem small_posSemidef : small.PosSemidef :=
  posSemidef_vecMulVec_self_star _

private theorem small_le_reference : small ≤ reference := by
  apply Matrix.le_iff.mpr
  simpa only [reference, add_sub_cancel_left] using
    (PosSemidef.diagonal (show ∀ i : Fin 3, 0 ≤ (![1, 2, 0] : Fin 3 → ℂ) i by
      intro i
      fin_cases i <;> norm_num))

private theorem reference_posSemidef : reference.PosSemidef :=
  (small_posSemidef.nonneg.trans small_le_reference).posSemidef

-- Both matrices are nonzero and have a common nonzero kernel vector.
example : small ≠ 0 ∧ reference ≠ 0 ∧
    (![0, 0, 1] : Fin 3 → ℂ) ≠ 0 ∧
    small *ᵥ ![0, 0, 1] = 0 ∧ reference *ᵥ ![0, 0, 1] = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 0 0) h
    norm_num [small, vecMulVec] at this
  · intro h
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 0 0) h
    norm_num [reference, small, vecMulVec, diagonal] at this
  · intro h
    have := congrArg (fun v : Fin 3 → ℂ ↦ v 2) h
    norm_num at this
  · ext i
    fin_cases i <;> norm_num [small, mulVec, dotProduct, Fin.sum_univ_succ, vecMulVec]
  · ext i
    fin_cases i <;>
      norm_num [reference, small, mulVec, dotProduct, Fin.sum_univ_succ, vecMulVec, diagonal]

-- Thus the main theorem applies to a genuinely singular pair, without
-- assuming their product is Hermitian or that the matrices commute.
example : small * reference ≠ reference * small ∧
    small * reference_posSemidef.supportInv * small ≤ small := by
  constructor
  · intro h
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 0 1) h
    norm_num [reference, small, Matrix.mul_apply, Fin.sum_univ_succ, vecMulVec, diagonal]
      at this
  · exact small_posSemidef.mul_supportInv_mul_le reference_posSemidef small_le_reference

-- Kernel and support statements are derived from order, with no supplied
-- kernel-inclusion or range-containment premise.
example : small * reference_posSemidef.supportProj = small ∧
    reference_posSemidef.supportProj * small = small :=
  ⟨small_posSemidef.mul_supportProj_eq_self_of_le reference_posSemidef small_le_reference,
    small_posSemidef.supportProj_mul_eq_self_of_le reference_posSemidef small_le_reference⟩

example : reference_posSemidef.supportInvSqrt * small *
    reference_posSemidef.supportInvSqrt ≤ reference_posSemidef.supportProj :=
  reference_posSemidef.supportInvSqrt_mul_mul_supportInvSqrt_le_supportProj small_le_reference

-- The all-zero reference and zero-dimensional ambient space are also allowed.
example : (0 : Matrix (Fin 3) (Fin 3) ℂ) * PosSemidef.zero.supportInv * 0 ≤ 0 :=
  PosSemidef.zero.mul_supportInv_mul_le PosSemidef.zero le_rfl

example (M ρ : Matrix (Fin 0) (Fin 0) ℂ) (hM : M.PosSemidef)
    (hρ : ρ.PosSemidef) (hMρ : M ≤ ρ) : M * hρ.supportInv * M ≤ M :=
  hM.mul_supportInv_mul_le hρ hMρ

end SupportInverseSandwichTest
