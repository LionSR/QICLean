/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.TensorPowerAction
import Mathlib.Algebra.Star.StarProjection

/-!
# The simultaneous symmetric projection

The average of the actual permutation operators of a finite group is a star
projection. Taking the group to be permutations of the copies and the one-copy
space to be the product of all five factors gives simultaneous symmetry,
including the middle physical factor Y.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `07-comparators.tex`, lines 427–439, comparator:defect-mass,
  at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix
open scoped BigOperators Matrix

namespace PermutationRepresentation

/-- A finite group average of the actual permutation matrices is a star
projection, including an empty coordinate set. This supplies the simultaneous
symmetric projection in OpenAI, `07-comparators.tex`, lines 427–439. -/
theorem isStarProjection_symProj
    {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    (φ : G →* Equiv.Perm X) : IsStarProjection (symProj φ) := by
  refine ⟨Matrix.ext_iff_mulVec.mpr (fun v =>
    (Matrix.mulVec_mulVec v (symProj φ) (symProj φ)).symm.trans
      (symProj_mulVec_of_mem φ (symProj_mulVec_mem φ v))), ?_⟩
  change (symProj φ)ᴴ = symProj φ
  simp only [symProj, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    conjTranspose_permOp, star_inv₀, star_natCast]
  exact congrArg (fun M : Matrix X X ℂ => (Fintype.card G : ℂ)⁻¹ • M)
    (Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl))

end PermutationRepresentation
