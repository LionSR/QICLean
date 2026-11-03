/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixRangeFrameMeasurable

/-!
# The actual ordered orthonormal basis of a finite matrix range

Restrict the selected ordered range frame to the range itself. This gives
an actual orthonormal basis, whose ambient coordinates are the previously
proved Borel frame. No measurability of a dependent space of basis objects
is asserted. This supports the sampling construction in ALVV,
arXiv:1602.08828v2, `l:rs`, lines 530–558.
-/

namespace Matrix

variable {d r : ℕ}

/-- The actual orthonormal basis obtained by restricting the selected
ordered range frame to the range of the same matrix. -/
noncomputable def rangeOrthonormalBasis
    (A : {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r}) :
    OrthonormalBasis (Fin r) ℂ (toEuclideanLin A.val).range := by
  let W := (toEuclideanLin A.val).range
  let v := rangeOrthonormalFrame A
  have hmem (i : Fin r) : v i ∈ W := by
    change rangeOrthonormalFrame A i ∈ (toEuclideanLin A.val).range
    rw [← span_rangeOrthonormalFrame A]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact OrthonormalBasis.mk ((orthonormal_rangeOrthonormalFrame A).codRestrict W hmem)
    ((Submodule.span_range_subtype_eq_top_iff W hmem).mpr (span_rangeOrthonormalFrame A)).ge

/-- The ambient coordinates of the actual range basis are exactly the
selected Borel range-frame coordinates. -/
theorem coe_rangeOrthonormalBasis
    (A : {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r}) (i : Fin r) :
    (rangeOrthonormalBasis A i : EuclideanSpace ℂ (Fin d)) = rangeOrthonormalFrame A i := by
  dsimp only [rangeOrthonormalBasis]
  exact congrArg (fun f : Fin r → (toEuclideanLin A.val).range ↦
    (f i : EuclideanSpace ℂ (Fin d))) (OrthonormalBasis.coe_mk _ _)

end Matrix
