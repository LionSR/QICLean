/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# Distances of images under a change of coordinates

Relabelling the coordinates of a square matrix `M` and of two vectors `x, y` along the same
bijection `E` does not change the Euclidean distance `‖M x - y‖`.

This is TNLean's `TNLean.Lattice.norm_reindex_mulVec_sub` (`Lattice/RegionalReset`, at commit
`707a50e56c`).

## Main results

* `Matrix.norm_reindex_mulVec_sub`.
-/

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Distances of images of vectors are unchanged by a simultaneous change of coordinates. -/
theorem norm_reindex_mulVec_sub (E : n ≃ m) (M : Matrix n n ℂ) (x y : n → ℂ) :
    ‖(WithLp.toLp 2 (reindex E E M *ᵥ (x ∘ E.symm)) : EuclideanSpace ℂ m) -
        WithLp.toLp 2 (y ∘ E.symm)‖ =
      ‖(WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℂ n) - WithLp.toLp 2 y‖ := by
  rw [reindex_mulVec, ← WithLp.toLp_sub, ← WithLp.toLp_sub]
  exact EuclideanSpace.norm_toLp_comp_equiv E.symm (M *ᵥ x - y)

end Matrix
