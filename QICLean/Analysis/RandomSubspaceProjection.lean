/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceRandomSampling

/-!
# Ambient projections of the existing Haar subspace sampler

The existing basis-parametrized random subspace is exactly the span of the
retained rotated basis vectors. Its actual ambient orthogonal projection
is their finite rank-one sum. These are geometric identities for the same
sampler in ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558; they assert no
measurability for an arbitrary varying basis and no adaptive probability.
-/

open QICLean.HaarProjection

namespace Submodule

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  [FiniteDimensional ℂ M] {W : Submodule ℂ M}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℂ M] [DecidableEq ι] in
/-- The existing basis embedding is the ambient finite basis expansion. -/
theorem basisEmbedding_apply_eq_sum (b : OrthonormalBasis ι ℂ W)
    (x : EuclideanSpace ℂ ι) :
    basisEmbedding b x = ∑ i, x i • (b i : M) := by
  change (b.repr.symm x : M) = _
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using
    congrArg (fun y : W ↦ (y : M)) (b.sum_repr_symm x).symm

omit [FiniteDimensional ℂ M] in
/-- The existing sampled subspace is precisely the span of the actual
retained Haar-rotated basis vectors. -/
theorem randomSubspace_eq_span_rotated_basis (b : OrthonormalBasis ι ℂ W)
    (A : Finset ι) (U : Matrix.unitaryGroup ι ℂ) :
    randomSubspace b A U = Submodule.span ℂ
      ((fun j ↦ basisEmbedding b (unitaryAction U (EuclideanSpace.basisFun ι ℂ j))) ''
        (A : Set ι)) := by
  rw [randomSubspace, coordinateSubspace, Submodule.map_span, Submodule.map_span]
  simp only [Set.image_image, EuclideanSpace.basisFun_apply]
  rfl

/-- The actual ambient projection of the existing sampled subspace is the
rank-one sum of its retained rotated orthonormal vectors. Empty retained
sets are allowed. -/
theorem starProjection_randomSubspace_eq_sum_rankOne (b : OrthonormalBasis ι ℂ W)
    (A : Finset ι) (U : Matrix.unitaryGroup ι ℂ) :
    (randomSubspace b A U).starProjection =
      ∑ j : A, InnerProductSpace.rankOne ℂ
        (basisEmbedding b (unitaryAction U (EuclideanSpace.basisFun ι ℂ j.val)))
        (basisEmbedding b (unitaryAction U (EuclideanSpace.basisFun ι ℂ j.val))) := by
  classical
  let v := fun j ↦ basisEmbedding b (unitaryAction U (EuclideanSpace.basisFun ι ℂ j))
  have hon : Orthonormal ℂ v :=
    ((EuclideanSpace.basisFun ι ℂ).orthonormal.comp_linearIsometry
      (unitaryAction U).toLinearIsometry).comp_linearIsometry (basisEmbedding b)
  have hproj := (OrthonormalBasis.span hon A).starProjection_eq_sum_rankOne
  rw [randomSubspace_eq_span_rotated_basis]
  simpa only [Finset.coe_image, OrthonormalBasis.span_apply, v] using hproj

end Submodule
