/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixRangeFrameMeasurable
import QICLean.Analysis.MatrixTensorCoordinates

/-!
# Canonical range frames in prescribed finite coordinates

A fixed equivalence of finite coordinates transports the existing canonical
Borel range frame. Its span is the actual matrix range. This auxiliary
allows collective trimming to use the physical configuration coordinates
in ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
-/

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] {d r : ℕ}

/-- Relabeling coordinates transports the actual matrix range. -/
theorem map_range_toEuclideanLin_submatrix (e : Fin d ≃ m) (A : Matrix m m ℂ) :
    (LinearMap.range (toEuclideanLin (A.submatrix e e))).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap =
      LinearMap.range (toEuclideanLin A) := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have heq : U.toLinearMap.comp (toEuclideanLin (A.submatrix e e)) =
      (toEuclideanLin A).comp U.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap (toEuclideanCLM_submatrix_intertwining e A)
  rw [← LinearMap.range_comp, heq, LinearMap.range_comp]
  simp only [LinearEquiv.range, Submodule.map_top]

/-- The existing canonical range frame transported to prescribed finite
coordinates through a fixed coordinate isometry. -/
noncomputable def rangeOrthonormalFrameInCoordinates (e : Fin d ≃ m)
    (A : {A : Matrix m m ℂ // A.rank = r}) : Fin r → EuclideanSpace ℂ m :=
  fun i ↦ LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    (rangeOrthonormalFrame ⟨A.val.submatrix e e, (rank_submatrix A.val e e).trans A.property⟩ i)

omit [DecidableEq m] in
/-- The transported range frame remains orthonormal, including rank zero. -/
theorem orthonormal_rangeOrthonormalFrameInCoordinates (e : Fin d ≃ m)
    (A : {A : Matrix m m ℂ // A.rank = r}) :
    Orthonormal ℂ (rangeOrthonormalFrameInCoordinates e A) :=
  (orthonormal_rangeOrthonormalFrame
    ⟨A.val.submatrix e e, (rank_submatrix A.val e e).trans A.property⟩).comp_linearIsometry
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearIsometry

/-- The transported frame spans the full actual matrix range in the
prescribed coordinates. -/
theorem span_rangeOrthonormalFrameInCoordinates (e : Fin d ≃ m)
    (A : {A : Matrix m m ℂ // A.rank = r}) :
    Submodule.span ℂ (Set.range (rangeOrthonormalFrameInCoordinates e A)) =
      (toEuclideanLin A.val).range := by
  change Submodule.span ℂ (Set.range
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap ∘
      rangeOrthonormalFrame ⟨A.val.submatrix e e, (rank_submatrix A.val e e).trans A.property⟩)) = _
  rw [Set.range_comp, ← Submodule.map_span, span_rangeOrthonormalFrame,
    map_range_toEuclideanLin_submatrix]

omit [DecidableEq m] in
/-- The actual transported range frame is Borel on each rank stratum;
the finite coordinate equivalence is fixed. -/
theorem measurable_rangeOrthonormalFrameInCoordinates (e : Fin d ≃ m) :
    Measurable (rangeOrthonormalFrameInCoordinates (r := r) e) := by
  have hmap : Measurable (fun A : {A : Matrix m m ℂ // A.rank = r} ↦
      (⟨A.val.submatrix e e, (rank_submatrix A.val e e).trans A.property⟩ :
        {A : Matrix (Fin d) (Fin d) ℂ // A.rank = r})) :=
    (show Continuous (fun A : {A : Matrix m m ℂ // A.rank = r} ↦
      A.val.submatrix e e) from by fun_prop).measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro i
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).continuous.measurable.comp
    ((measurable_pi_apply i).comp (measurable_rangeOrthonormalFrame.comp hmap))

end Matrix
