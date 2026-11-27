/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Dyadic.DyadicLayers
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Analysis.Convex.Topology
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Closures of dyadic cells and layers

A half-open dyadic cell has a closed rectangular closure. Since each actual
layer is a finite union of cells, its closure is the union of these closed
rectangles. This uses closure of a finite union, rather than a rule for the
closure of a set difference. The formulas are preliminary to the layer-distance
estimates, which are not established here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families` and
`geometry:layer-distance`, lines 151–189.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace ManyBody

/-- The closure of a translated half-open dyadic cell is its closed rectangle.
Source: area-law Section 11, `prop:two-families`, lines 151–185. -/
theorem closure_dyadicCell (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    closure (dyadicCell o k z) =
      Set.Icc (o.1 + (2 : ℝ) ^ k * z.1) (o.1 + (2 : ℝ) ^ k * (z.1 + 1)) ×ˢ
        Set.Icc (o.2 + (2 : ℝ) ^ k * z.2) (o.2 + (2 : ℝ) ^ k * (z.2 + 1)) := by
  have h (a : ℝ) (i : ℤ) :
      a + (2 : ℝ) ^ k * i ≠ a + (2 : ℝ) ^ k * (i + 1) := by
    have hp : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
    linarith
  rw [dyadicCell, closure_prod_eq, closure_Ico (h _ _), closure_Ico (h _ _)]

/-- The closed rectangle of a dyadic cell is convex. Source: area-law Section 11,
`prop:two-families`, lines 151–185. -/
theorem convex_closure_dyadicCell (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    Convex ℝ (closure (dyadicCell o k z)) := by
  rw [closure_dyadicCell]
  exact (convex_Icc _ _).prod (convex_Icc _ _)

/-- The closure of a dyadic layer is the finite union of its cell closures.
Source: area-law Section 11, `prop:two-families`, `geometry:layer-distance`,
lines 179–189. -/
theorem closure_dyadicLayer_eq_iUnion (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    closure (dyadicLayer o k Z C) =
      ⋃ z ∈ dyadicLayerIndices o k Z C, closure (dyadicCell o k z) := by
  rw [dyadicLayer_eq_iUnion, Finset.closure_biUnion]

end ManyBody

section
namespace ManyBody
section SideSubdivision

/-- A corner of the actual translated dyadic cell, with each endpoint chosen by
a binary coordinate. Source: area-law Section 11, lines 299–306 and 352–356. -/
def dyadicCellCorner (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (ε : Fin 2 × Fin 2) : ℝ × ℝ :=
  (o.1 + (2 : ℝ) ^ ℓ * ((z.1 : ℝ) + ε.1.val),
    o.2 + (2 : ℝ) ^ ℓ * ((z.2 : ℝ) + ε.2.val))

theorem dyadicCellCorner_mem_closure (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (ε : Fin 2 × Fin 2) :
    dyadicCellCorner o ℓ z ε ∈ closure (dyadicCell o ℓ z) := by
  have hbound (a : ℝ) (i : ℤ) (e : Fin 2) :
      a + (2 : ℝ) ^ ℓ * ((i : ℝ) + e.val) ∈
        Set.Icc (a + (2 : ℝ) ^ ℓ * i) (a + (2 : ℝ) ^ ℓ * (i + 1)) := by
    have he0 : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
    have he1 : (e.val : ℝ) ≤ 1 := by exact_mod_cast (show e.val ≤ 1 by omega)
    have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
    constructor <;> nlinarith
  rw [closure_dyadicCell]
  exact ⟨hbound o.1 z.1 ε.1, hbound o.2 z.2 ε.2⟩

end SideSubdivision
end ManyBody
end

section
namespace ManyBody
section ElementarySideOpponents

/-- The corner of the closed axis-parallel rectangle with opposite corners `a`
and `b` selected by `ε`, where the coordinate `0` picks `a` and `1` picks `b`.
Source: area-law Section 11, lines 299–316. -/
def rectangleCorner (a b : ℝ × ℝ) (ε : Fin 2 × Fin 2) : ℝ × ℝ :=
  (if ε.1.val = 0 then a.1 else b.1, if ε.2.val = 0 then a.2 else b.2)

/-- The lower-left corner of a dyadic cell lies strictly below and to the left
of its upper-right corner. Source: area-law Section 11, lines 299–310. -/
theorem dyadicCellCorner_lt (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    (dyadicCellCorner o ℓ z (0, 0)).1 < (dyadicCellCorner o ℓ z (1, 1)).1 ∧
      (dyadicCellCorner o ℓ z (0, 0)).2 < (dyadicCellCorner o ℓ z (1, 1)).2 := by
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  constructor <;> norm_num [dyadicCellCorner]

/-- The interior of a dyadic cell is the open rectangle spanned by its extreme
corners. Source: area-law Section 11, lines 299–310. -/
theorem interior_dyadicCell_eq_corners (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    interior (dyadicCell o ℓ z) =
      Set.Ioo (dyadicCellCorner o ℓ z (0, 0)).1 (dyadicCellCorner o ℓ z (1, 1)).1 ×ˢ
        Set.Ioo (dyadicCellCorner o ℓ z (0, 0)).2 (dyadicCellCorner o ℓ z (1, 1)).2 := by
  simp [dyadicCell, interior_prod_eq, interior_Ico, dyadicCellCorner]

/-- The closure of a dyadic cell is the closed rectangle spanned by its extreme
corners. Source: area-law Section 11, lines 299–310. -/
theorem closure_dyadicCell_eq_corners (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    closure (dyadicCell o ℓ z) =
      Set.Icc (dyadicCellCorner o ℓ z (0, 0)).1 (dyadicCellCorner o ℓ z (1, 1)).1 ×ˢ
        Set.Icc (dyadicCellCorner o ℓ z (0, 0)).2 (dyadicCellCorner o ℓ z (1, 1)).2 := by
  simp [closure_dyadicCell, dyadicCellCorner]

/-- The rectangle corners spanned by the extreme corners of a dyadic cell are
its four corners. Source: area-law Section 11, lines 299–310. -/
theorem rectangleCorner_eq_dyadicCellCorner (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (ε : Fin 2 × Fin 2) :
    rectangleCorner (dyadicCellCorner o ℓ z (0, 0)) (dyadicCellCorner o ℓ z (1, 1)) ε =
      dyadicCellCorner o ℓ z ε := by
  rcases ε with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> norm_num [rectangleCorner, dyadicCellCorner]

end ElementarySideOpponents
end ManyBody
end
