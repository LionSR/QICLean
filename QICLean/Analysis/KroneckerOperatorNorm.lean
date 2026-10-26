/-
Copyright (c) 2026 TNLean and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors, QICLean contributors
-/
import QICLean.Algebra.MatrixKroneckerEmbed
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norm after tensoring with an identity

Tensoring a square complex matrix with the identity of a nonempty finite space
preserves its Euclidean operator norm. The matrix space itself may have dimension zero.

The conclusion strengthens the reverse inequality proved in
`TNLean/MPS/AreaLaw/ViableSet/Gluing.lean`, commit
`111c9fe461af184e1aa20be8091ec1d1a775a68a`. The proof uses the existing
Kronecker star-algebra homomorphism and Mathlib's isometry theorem for injective
complex C-star-algebra homomorphisms, instead of extracting an isometric corner.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

/-- Tensoring a complex matrix with an identity on a nonempty finite space preserves
its Euclidean operator norm, including when the matrix has no rows or columns. -/
theorem l2_opNorm_one_kronecker {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] (K : Matrix Y Y ℂ) :
    ‖(1 : Matrix X X ℂ) ⊗ₖ K‖ = ‖K‖ := by
  change ‖rightKroneckerEmbed (m := X) K‖ = ‖K‖
  apply NonUnitalStarAlgHom.norm_map
  intro A B h
  ext i j
  simpa using congrFun (congrFun h (Classical.choice ‹Nonempty X›, i))
    (Classical.choice ‹Nonempty X›, j)

end Matrix
