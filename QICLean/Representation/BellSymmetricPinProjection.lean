/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionSymmetry
import QICLean.Representation.TrivialLabel
import QICLean.Algebra.OrthogonalProjection

/-!
# The symmetric projection after the actual Bell insertion

Insert a unit Bell-coordinate vector by the specified tensor-power insertion
in the original physical coordinates. Conjugating the exterior symmetry
projection by this actual isometry gives an orthogonal projection on the
original coordinate space. The two auxiliary coordinate types remain
distinct, and zero copies are included.

The assertion is obtained from the existing finite-group symmetry projection
and the existing conjugation theorem for star projections. It introduces no
new range construction or hypothesis asserting that the insertion is an
isometry.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Matrix PermutationRepresentation FiniteProduct

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

omit [DecidableEq C] in
/-- The literal Bell insertion carries the exterior symmetric projection to
an orthogonal projection in the original physical coordinates. Its isometry
property is derived from the unit norm of the inserted vector.

Source: area-law manuscript, `07-comparators.tex`, lines 283–308,
`comparator:pinned-metric`. -/
theorem isStarProjection_bellInsertion_symProj (k : ℕ)
    (b : (Configuration β X × C) → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion (compressedSiteSpace β X R)
      (Configuration β X × C) k b).submatrix e id
    let Pe := symProj (copyPerm
      ((v : Option ↥(Xᶜ)) → compressedSiteSpace β X R v) k)
    IsStarProjection (J * Pe * Jᴴ) := by
  intro e J Pe
  have hJ : Jᴴ * J = 1 := isIsometry_bellInsertion β X C R k b hb
  have hU : Jᴴ * (Jᴴ)ᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hJ
  simpa only [Matrix.conjTranspose_conjTranspose] using
    IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
      ((exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
        (X := Config k (compressedSiteSpace β X R))).elim (fun l hl ↦
          Eq.mp (congrArg IsStarProjection (hl (copyPerm
            ((v : Option ↥(Xᶜ)) → compressedSiteSpace β X R v) k)))
            ⟨labelProj_mul_self _ l, (isHermitian_labelProj _ l).isSelfAdjoint⟩)) Jᴴ hU

end TensorPower
