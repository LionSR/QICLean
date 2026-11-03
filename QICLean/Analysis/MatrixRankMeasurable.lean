/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixRankClosed
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Borel gluing along matrix-rank strata

Finite complex matrix rank is Borel. A map whose restrictions to the
rank strata of a Borel matrix-valued map are Borel is therefore Borel.
This elementary auxiliary permits varying input dimensions in ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558.
-/

open MeasureTheory

namespace Matrix

/-- Finite complex matrix rank is a Borel function. -/
theorem measurable_rank {m n : Type*} [Finite m] [Fintype n] :
    Measurable (Matrix.rank : Matrix m n ℂ → ℕ) :=
  lowerSemicontinuous_rank.measurable

end Matrix

/-- Borel restrictions to the matrix-rank strata give a Borel map on the
whole domain. No measurable choice of bases is assumed. -/
theorem measurable_of_matrix_rank_strata {X Y m n : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Finite m] [Fintype n]
    {P : X → Matrix m n ℂ} (hP : Measurable P) {f : X → Y}
    (hf : ∀ r : ℕ, Measurable (fun x : {x : X // (P x).rank = r} ↦ f x.val)) :
    Measurable f := by
  intro s hs
  have hstratum (r : ℕ) : MeasurableSet {x : X | (P x).rank = r} :=
    measurableSet_eq_fun (Matrix.measurable_rank.comp hP) measurable_const
  have heq : f ⁻¹' s = ⋃ r : ℕ,
      Subtype.val '' ((fun x : {x : X // (P x).rank = r} ↦ f x.val) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      exact ⟨(P x).rank, ⟨x, rfl⟩, hx, rfl⟩
    · rintro ⟨r, y, hy, rfl⟩
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun r ↦ (hstratum r).subtype_image (hf r hs)
