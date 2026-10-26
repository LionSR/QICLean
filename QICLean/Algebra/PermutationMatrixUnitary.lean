/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitarity of permutation matrices

A complex permutation matrix belongs to the unitary group.

Adapted without changes to the theorem from TNLean, `TNLean/Algebra/PermutationMatrixUnitary.lean`,
commit `d289fdbbf7205860aa3db1454156780bd780e96a`.
-/

/- Migration note: TNLean retains its original declaration until its QICLean pin includes this
module. That coordinated update must replace imports of the TNLean module by this module and
delete the original declaration. The name is preserved by relocation, without an alias. -/

open scoped Matrix

namespace Equiv.Perm

/-- A complex permutation matrix is unitary. -/
theorem permMatrix_mem_unitaryGroup {n : Type*} [DecidableEq n] [Fintype n]
    (σ : Equiv.Perm n) :
    permMatrix ℂ σ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

end Equiv.Perm
