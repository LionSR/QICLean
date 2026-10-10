/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OrthogonalResolutionCfc

/-!
# Functional calculus of a two-sector comparison operator

The complementary projections of a self-adjoint idempotent form a finite
orthogonal resolution of the identity. Functional calculus of its affine
transform therefore acts by the scalar value on each sector. The scalar
function is arbitrary, and its two displayed arguments may coincide.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*
  (September 24, 2026), `07-comparators.tex`, lines 603–640,
  in the proof of `comparator:tree-log-lower`.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The functional calculus of a self-adjoint idempotent's affine transform
acts by the two scalar values on the corresponding sectors. This computation
is used in the two-sector comparison of the area-law paper,
`07-comparators.tex`, lines 603–640. -/
theorem cfc_affine_of_isSelfAdjoint_isIdempotentElem
    (q : Matrix n n ℂ) (hq : IsSelfAdjoint q) (hqq : IsIdempotentElem q)
    (b d : ℝ) (f : ℝ → ℝ) :
    cfc f (b • (1 : Matrix n n ℂ) + (d - b) • q) =
      f b • (1 - q) + f d • q := by
  let sectors : Bool → Matrix n n ℂ := fun j => if j then q else 1 - q
  have hproj : IsStarProjection q := ⟨hqq, hq⟩
  have hresolution : IsOrthogonalResolution sectors := by
    constructor
    · intro i j
      cases i <;> cases j <;>
        simp only [sectors, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
          hproj.isIdempotentElem.eq, hproj.one_sub.isIdempotentElem.eq,
          hproj.mul_one_sub_self, hproj.one_sub_mul_self]
    · simp only [Fintype.sum_bool, sectors, Bool.false_eq_true, ite_true, ite_false]
      rw [← add_sub_assoc, add_sub_cancel_left]
  have hHermitian : ∀ j, (sectors j).IsHermitian :=
    fun j => Bool.rec hproj.one_sub.isSelfAdjoint.isHermitian hq.isHermitian j
  have hcalc := hresolution.cfc_hom hHermitian f (fun j => if j then d else b)
  have hoperator :
      hresolution.hom (fun j => ((if j then d else b : ℝ) : ℂ)) =
        b • (1 : Matrix n n ℂ) + (d - b) • q := by
    simp only [IsOrthogonalResolution.hom_apply, Fintype.sum_bool, sectors,
      Bool.false_eq_true, ite_true, ite_false, Complex.coe_smul]
    rw [smul_sub, sub_smul]
    abel
  rw [hoperator] at hcalc
  simpa only [IsOrthogonalResolution.hom_apply, Fintype.sum_bool, sectors,
    Bool.false_eq_true, ite_true, ite_false, Complex.coe_smul, add_comm] using hcalc

end Matrix
