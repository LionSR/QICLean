/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ViableSubspaceTrimming
import QICLean.Channel.SchmidtMarginalAction

/-!
# Collective trimming is independent of the orthonormal basis

The marginal at each cut depends only on the original Gram operator.
Thus families with the same Gram operator give the same literal trimming
projections. In particular, collective trimming does not depend on the
orthonormal basis used to describe its input subspace.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
-/

open Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Cutting the physical sites and then tracing the remaining physical
sites and environment is the regional partial trace of the original left
marginal. This identifies the reduced operators in ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_cutEnvVector {β : Type*} [Fintype β]
    (D : Finset V) (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    leftMarginal (cutEnvVector D w) = partialTraceRight (cutOperator D (leftMarginal w)) := by
  ext x y
  simp only [leftMarginal, mul_apply, conjTranspose_apply, schmidtCoeffMatrix_apply,
    cutEnvVector_apply, partialTraceRight_apply, reindex_apply,
    submatrix_apply, Fintype.sum_prod_type]

/-- After an arbitrary physical operator, every cut marginal is determined
by the original Gram operator. Used for the successive projections of ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_cutEnvVector_leftApply {β : Type*} [Fintype β]
    (D : Finset V) (P : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    leftMarginal (cutEnvVector D (leftApply P w)) =
      partialTraceRight (cutOperator D (P * leftMarginal w * Pᴴ)) := by
  rw [leftMarginal_cutEnvVector, leftMarginal_leftApply]

/-- Families with equal Gram operators give the same literal products of
successive trimming projections. No monotonicity of the cuts or positive
threshold is needed for this identity. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem trimProj_eq_of_leftMarginal_stackVector_eq {s t : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n))
    (v : Fin t → EuclideanSpace ℂ (SiteConfig n))
    (h : leftMarginal (stackVector u) = leftMarginal (stackVector v)) (j : ℕ) :
    trimProj D xi u j = trimProj D xi v j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [trimProj, ih, leftMarginal_cutEnvVector_leftApply, h]

omit [Fintype V] [DecidableEq V] in
/-- The Gram operator of the stacked family is the sum of its rank-one
operators. This is the original operator determining ALVV collective
trimming, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_stackVector {s : ℕ}
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) :
    leftMarginal (stackVector u) =
      ∑ i, vecMulVec (WithLp.ofLp (u i)) (star (WithLp.ofLp (u i))) := by
  ext x y
  simp only [leftMarginal, mul_apply, conjTranspose_apply, schmidtCoeffMatrix_apply,
    stackVector, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply]

/-- For an orthonormal basis of a subspace, the original stacked Gram
operator is exactly its orthogonal projection. Thus the input to ALVV
collective trimming depends only on the subspace; see
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem toEuclideanLin_leftMarginal_stackVector_orthonormalBasis {s : ℕ}
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (b : OrthonormalBasis (Fin s) ℂ S) :
    toEuclideanLin (leftMarginal (stackVector fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n)))) =
      S.starProjection.toLinearMap := by
  rw [leftMarginal_stackVector, map_sum]
  have hstar := congrArg
    (fun P : EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n) ↦
      P.toLinearMap) b.starProjection_eq_sum_rankOne
  rw [hstar]
  simp only [ContinuousLinearMap.toLinearMap_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg toEuclideanLin
    (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℂ)
      (x := (b i : EuclideanSpace ℂ (SiteConfig n)))
      (y := (b i : EuclideanSpace ℂ (SiteConfig n))))
  simpa using h.symm

/-- The successive collective-trimming projections are independent of
which orthonormal basis describes the original subspace. This is the
basis invariance of ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem trimProj_eq_of_orthonormalBasis {s t : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (b : OrthonormalBasis (Fin s) ℂ S) (c : OrthonormalBasis (Fin t) ℂ S) (j : ℕ) :
    trimProj D xi (fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n))) j =
      trimProj D xi (fun i ↦ (c i : EuclideanSpace ℂ (SiteConfig n))) j := by
  apply trimProj_eq_of_leftMarginal_stackVector_eq
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_leftMarginal_stackVector_orthonormalBasis,
    toEuclideanLin_leftMarginal_stackVector_orthonormalBasis]

/-- The actual trimmed span is the image of the original subspace under
its literal product of collective projections. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem trimSubspace_eq_map_of_orthonormalBasis {s : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (b : OrthonormalBasis (Fin s) ℂ S) (j : ℕ) :
    trimSubspace D xi (fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n))) j =
      S.map (toEuclideanLin
        (trimProj D xi (fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n))) j)) := by
  have hspan : Submodule.span ℂ
      (Set.range fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n))) = S := by
    simpa only [← Set.range_comp, Function.comp_def] using
      (Submodule.span_val_image_eq_iff S (Set.range b)).mpr b.toBasis.span_eq
  rw [trimSubspace, Set.range_comp', ← Submodule.map_span, hspan]

/-- The literal trimmed subspace is independent of its prescribed
orthonormal basis, including the zero subspace and zero or negative
thresholds. Source: ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem trimSubspace_eq_of_orthonormalBasis {s t : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (b : OrthonormalBasis (Fin s) ℂ S) (c : OrthonormalBasis (Fin t) ℂ S) (j : ℕ) :
    trimSubspace D xi (fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n))) j =
      trimSubspace D xi (fun i ↦ (c i : EuclideanSpace ℂ (SiteConfig n))) j := by
  rw [trimSubspace_eq_map_of_orthonormalBasis, trimSubspace_eq_map_of_orthonormalBasis,
    trimProj_eq_of_orthonormalBasis D xi b c j]

end Entropy
