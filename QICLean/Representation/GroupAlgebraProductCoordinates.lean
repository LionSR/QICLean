/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.PermutationRepresentation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Group-algebra operators in product coordinates

An equivariant coordinate identification with a product, on whose first
factor the group acts trivially, identifies every group-algebra operator with
the identity tensored with the operator on the second factor. The extension
from group elements uses linear induction on the group algebra and does not
require the group itself to be finite.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, lines 14–27 and 73–80;
  application to the actual auxiliary label in `07-comparators.tex`,
  lines 255–281 and 332–354.

-/

open scoped Matrix Kronecker

namespace PermutationRepresentation

variable {G Z A B : Type*} [Group G]
variable [Fintype Z] [Fintype B]
variable [DecidableEq Z] [DecidableEq A] [DecidableEq B]

/-- An actual product-coordinate intertwining of permutation actions extends
to every element of the group algebra. -/
theorem groupAlgebraRep_submatrix_of_prod_action
    (φ : G →* Equiv.Perm Z) (ψ : G →* Equiv.Perm B) (e : Z ≃ A × B)
    (he : ∀ g z, e (φ g z) = ((e z).1, ψ g (e z).2))
    (a : MonoidAlgebra ℂ G) :
    (groupAlgebraRep φ a).submatrix e.symm e.symm =
      (1 : Matrix A A ℂ) ⊗ₖ groupAlgebraRep ψ a := by
  have hperm (g : G) : (permOp φ g).submatrix e.symm e.symm =
      (1 : Matrix A A ℂ) ⊗ₖ permOp ψ g := by
    ext x y
    have hxy : φ g (e.symm y) = e.symm x ↔
        y.1 = x.1 ∧ ψ g y.2 = x.2 := by
      constructor
      · intro h
        have h' := congrArg e h
        simp only [he, Equiv.apply_symm_apply] at h'
        exact Prod.mk.inj h'
      · rintro ⟨h₁, h₂⟩
        apply e.injective
        simp only [he, Equiv.apply_symm_apply, h₁, h₂]
    simp only [Matrix.submatrix_apply, permOp_apply_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
    simp only [hxy]
    by_cases h₁ : y.1 = x.1
    · simp [h₁]
    · simp [h₁, Ne.symm h₁]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, Matrix.submatrix_add, Pi.add_apply, Matrix.kronecker_add, ha, hb]
  | single g c =>
    simp only [groupAlgebraRep_single, Matrix.submatrix_smul, Pi.smul_apply, hperm,
      Matrix.kronecker_smul]

end PermutationRepresentation
