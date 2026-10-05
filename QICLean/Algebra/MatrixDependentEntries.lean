/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.Basic

/-!
# Entries of matrices on varying index spaces

A dependent matrix family has the same entries after identifying its parameter and the
corresponding row and column coordinates. The coordinate identifications may be heterogeneous.
-/

namespace Matrix

/-- Entries of a dependent family of matrices agree once the index equation and
both coordinate identifications are given heterogeneously. -/
theorem entry_eq_of_heq {ι : Type*} {m n : ι → Type*} {R : Type*}
    (M : (i : ι) → Matrix (m i) (n i) R) {i j : ι} (h : i = j)
    {x : m i} {y : n i} {x' : m j} {y' : n j} (hx : x ≍ x') (hy : y ≍ y') :
    M i x y = M j x' y' := by
  subst h
  cases hx
  cases hy
  rfl

end Matrix
