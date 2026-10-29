/-
Copyright (c) 2026 TNLean and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors, QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Matrix expectations under a change of coordinates

Relabelling the coordinates of a vector and the rows and columns of a matrix
through the same equivalence preserves their expectation pairing.

The statement is adapted from `TNLean/MPS/AreaLaw/ViableSet/Gluing.lean`, commit
`111c9fe461af184e1aa20be8091ec1d1a775a68a`, with a public matrix namespace and
a proof using Mathlib's coordinate isometry and matrix-vector transport.
-/

open scoped InnerProductSpace

namespace Matrix

/-- Relabelling a vector and both indices of a matrix preserves the expectation pairing. -/
theorem inner_toEuclideanLin_reindex {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (M : Matrix X X ℂ) (ψ : EuclideanSpace ℂ X) :
    ⟪WithLp.toLp 2 (WithLp.ofLp ψ ∘ e.symm),
        toEuclideanLin (reindex e e M) (WithLp.toLp 2 (WithLp.ofLp ψ ∘ e.symm))⟫_ℂ =
      ⟪ψ, toEuclideanLin M ψ⟫_ℂ := by
  convert (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).inner_map_map ψ
    (toEuclideanLin M ψ) using 2
  · rfl
  · change WithLp.toLp 2 (M.submatrix e.symm e.symm *ᵥ (WithLp.ofLp ψ ∘ e.symm)) =
      WithLp.toLp 2 ((M *ᵥ WithLp.ofLp ψ) ∘ e.symm)
    simpa [Function.comp_assoc] using congrArg (WithLp.toLp 2)
      (submatrix_mulVec_equiv M (WithLp.ofLp ψ ∘ e.symm) e.symm e.symm)

end Matrix
