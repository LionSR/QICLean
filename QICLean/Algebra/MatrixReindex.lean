/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing complex matrix star algebras

Simultaneous reindexing of rows and columns gives a star-algebra equivalence.
Its underlying map is `Matrix.reindex`; inversion and composition agree with
those of the index equivalences.
-/

namespace Matrix

variable {m n o : Type*} [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n] [Fintype o] [DecidableEq o]

/-- Reindexing both matrix indices along the same equivalence is a
star-algebra equivalence. -/
noncomputable def reindexStarAlgEquiv (e : m ≃ n) :
    Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (reindexAlgEquiv ℂ ℂ e) fun M ↦ by
    change reindex e e (star M) = star (reindex e e M)
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_reindex]

@[simp]
theorem reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m ℂ) :
    reindexStarAlgEquiv e M = reindex e e M := rfl

@[simp]
theorem symm_reindexStarAlgEquiv (e : m ≃ n) :
    (reindexStarAlgEquiv e).symm = reindexStarAlgEquiv e.symm := rfl

@[simp]
theorem reindexStarAlgEquiv_trans_reindexStarAlgEquiv (e : m ≃ n) (f : n ≃ o) :
    (reindexStarAlgEquiv e).trans (reindexStarAlgEquiv f) =
      reindexStarAlgEquiv (e.trans f) := rfl

end Matrix
