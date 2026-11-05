/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixRangeOrthonormalBasis
import QICLean.Analysis.RandomSubspaceProjection

/-!
# A joint Borel projector for the existing canonical-frame sampler

On a fixed matrix-rank stratum, the actual orthonormal range basis defines
the existing randomSubspace sampler. Its ambient orthogonal projector is
the finite Gram sum of the retained rotated frame columns, and is Borel
jointly in the input matrix and the unitary. No parallel sampler is defined.
This supports ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558, without
asserting a varying arbitrary-basis map, Haar-law comparison or adaptive law.
-/

open MeasureTheory QICLean.HaarProjection
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {d r : ℕ}

/-- The selected range-frame columns after the actual coordinate unitary. -/
def rotatedRangeFrame (P : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r})
    (U : unitaryGroup (Fin r) ℂ) : Fin r → EuclideanSpace ℂ (Fin d) :=
  fun j ↦ ∑ i, (U : Matrix (Fin r) (Fin r) ℂ) i j • rangeOrthonormalFrame P i

/-- The finite rotated frame is exactly the existing basis embedding of
the existing unitary action, for the constructed actual range basis. -/
theorem basisEmbedding_rangeOrthonormalBasis_unitaryAction_eq
    (P : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r})
    (U : unitaryGroup (Fin r) ℂ) (j : Fin r) :
    Submodule.basisEmbedding (rangeOrthonormalBasis P)
        (unitaryAction U (EuclideanSpace.basisFun (Fin r) ℂ j)) = rotatedRangeFrame P U j := by
  rw [Submodule.basisEmbedding_apply_eq_sum]
  simp_rw [coe_rangeOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  have hcoord : unitaryAction U (EuclideanSpace.basisFun (Fin r) ℂ j) i =
      (U : Matrix (Fin r) (Fin r) ℂ) i j := by
    change ((U : Matrix (Fin r) (Fin r) ℂ) *ᵥ
      (EuclideanSpace.basisFun (Fin r) ℂ j).ofLp) i = _
    simp [EuclideanSpace.basisFun_apply, Matrix.mulVec_single]
  rw [hcoord]

/-- The ambient matrix of the actual existing sampled-subspace projection
is the finite Gram sum of the retained rotated range-frame columns. -/
theorem randomSubspace_rangeOrthonormalBasis_projection_eq_sum
    (P : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r})
    (A : Finset (Fin r)) (U : unitaryGroup (Fin r) ℂ) :
    (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (Submodule.randomSubspace (rangeOrthonormalBasis P) A U).starProjection =
      ∑ j : A, vecMulVec (rotatedRangeFrame P U j.val).ofLp
        (star (rotatedRangeFrame P U j.val).ofLp) := by
  rw [Submodule.starProjection_randomSubspace_eq_sum_rankOne, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [basisEmbedding_rangeOrthonormalBasis_unitaryAction_eq]
  exact InnerProductSpace.symm_toEuclideanLin_rankOne _ _

/-- The rotated frame coordinates are Borel jointly in the fixed-rank
input matrix and the coordinate unitary. -/
theorem measurable_rotatedRangeFrame :
    Measurable (fun p : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r} ×
      unitaryGroup (Fin r) ℂ ↦ rotatedRangeFrame p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun p : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r} ×
    unitaryGroup (Fin r) ℂ ↦ ∑ i, (p.2 : Matrix (Fin r) (Fin r) ℂ) i j •
      rangeOrthonormalFrame p.1 i)
  apply Finset.measurable_sum
  intro i _
  have hframe : Measurable (fun p : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r} ×
      unitaryGroup (Fin r) ℂ ↦ rangeOrthonormalFrame p.1 i) := (measurable_pi_apply i).comp
    ((measurable_rangeOrthonormalFrame (d := d) (r := r)).comp measurable_fst)
  have hunitary : Measurable (fun p : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r} ×
      unitaryGroup (Fin r) ℂ ↦ (p.2 : Matrix (Fin r) (Fin r) ℂ)) :=
    (show Continuous (fun U : unitaryGroup (Fin r) ℂ ↦
      (U : Matrix (Fin r) (Fin r) ℂ)) from continuous_subtype_val).measurable.comp measurable_snd
  exact hunitary.eval_matrix.smul hframe

/-- The actual existing canonical-range-basis sampler has a Borel ambient
projector jointly in its input and unitary. The retained coordinate set is
fixed, so the statement includes the first min(s,r) coordinates and r=0. -/
theorem measurable_randomSubspace_rangeOrthonormalBasis_projection
    (A : Finset (Fin r)) :
    Measurable (fun p : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r} ×
      unitaryGroup (Fin r) ℂ ↦ (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (Submodule.randomSubspace (rangeOrthonormalBasis p.1) A p.2).starProjection) := by
  have heq : (fun p : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r} ×
      unitaryGroup (Fin r) ℂ ↦ (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (Submodule.randomSubspace (rangeOrthonormalBasis p.1) A p.2).starProjection) =
      (fun p ↦ ∑ j : A, vecMulVec (rotatedRangeFrame p.1 p.2 j.val).ofLp
        (star (rotatedRangeFrame p.1 p.2 j.val).ofLp)) := by
    funext p
    exact randomSubspace_rangeOrthonormalBasis_projection_eq_sum p.1 A p.2
  rw [heq]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.of_eval_matrix
  intro a b
  have hz := (measurable_pi_apply j.val).comp (measurable_rotatedRangeFrame (d := d) (r := r))
  have hc := (WithLp.measurable_ofLp 2 (Fin d → ℂ)).comp hz
  have hstar : Measurable (fun z : ℂ ↦ star z) :=
    (by fun_prop : Continuous (star : ℂ → ℂ)).measurable
  exact ((measurable_pi_apply a).comp hc).mul (hstar.comp ((measurable_pi_apply b).comp hc))

end Matrix
