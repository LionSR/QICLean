/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Finite matrix actions in tensor coordinates

The product orthonormal basis identifies a Kronecker matrix with the continuous
tensor product of its matrix actions. Relabeling finite coordinates transports
this identity to finite sums. Exchanging the tensor factors gives the same
intertwining identity with the factors reversed.

These coordinate identities support the tensor decompositions in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. They make no spectral,
physical representation, or running-time assertion. Empty finite coordinate
types and empty finite sums are included.
-/

open scoped BigOperators Kronecker TensorProduct

namespace Matrix

/-- In the product orthonormal basis, the Kronecker product acts as the
continuous tensor product of the two matrix actions. The two coordinate
spaces may have dimension zero. This is the continuous Euclidean form of
`Matrix.toLin_kronecker`. -/
theorem toEuclideanCLM_kronecker_intertwining
    {𝕜 X Y : Type*} [RCLike 𝕜] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (A : Matrix X X 𝕜) (B : Matrix Y Y 𝕜) :
    let e := ((EuclideanSpace.basisFun X 𝕜).tensorProduct
      (EuclideanSpace.basisFun Y 𝕜)).repr
    e.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        TensorProduct.mapL (toEuclideanCLM (𝕜 := 𝕜) (n := X) A)
          (toEuclideanCLM (𝕜 := 𝕜) (n := Y) B) =
      toEuclideanCLM (𝕜 := 𝕜) (n := X × Y) (A ⊗ₖ B) ∘L
        e.toContinuousLinearEquiv.toContinuousLinearMap := by
  intro e
  let bX := EuclideanSpace.basisFun X 𝕜
  let bY := EuclideanSpace.basisFun Y 𝕜
  let b := bX.tensorProduct bY
  have hmap : toLin b.toBasis b.toBasis (A ⊗ₖ B) =
      TensorProduct.map (toEuclideanLin A) (toEuclideanLin B) := by
    simpa only [b, OrthonormalBasis.toBasis_tensorProduct,
      toEuclideanLin_eq_toLin_orthonormal] using
      (toLin_kronecker bX.toBasis bY.toBasis bX.toBasis bY.toBasis A B)
  ext z i
  simp only [ContinuousLinearMap.comp_apply, TensorProduct.mapL_apply]
  change (b.repr (TensorProduct.map (toEuclideanLin A) (toEuclideanLin B) z)) i =
    ((A ⊗ₖ B) *ᵥ fun j ↦ b.repr z j) i
  have h := congrFun (repr_toLin b.toBasis b.toBasis (A ⊗ₖ B) z) i
  rw [hmap] at h
  simpa only [mulVec, dotProduct, OrthonormalBasis.coe_toBasis_repr_apply] using h

/-- Relabeling finite Euclidean coordinates intertwines the corresponding
matrix actions. This is the continuous Euclidean form of
`Matrix.submatrix_mulVec_equiv`. Empty coordinate types are included. -/
theorem toEuclideanCLM_submatrix_intertwining
    {𝕜 Z V : Type*} [RCLike 𝕜] [Fintype Z] [Fintype V]
    [DecidableEq Z] [DecidableEq V] (e : Z ≃ V) (P : Matrix V V 𝕜) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e
    U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := 𝕜) (n := Z) (P.submatrix e e) =
      toEuclideanCLM (𝕜 := 𝕜) (n := V) P ∘L
        U.toContinuousLinearEquiv.toContinuousLinearMap := by
  intro U
  ext x i
  change ((P.submatrix e e) *ᵥ (fun j ↦ x j)) (e.symm i) =
    (P *ᵥ (fun j ↦ x (e.symm j))) i
  simpa only [Function.comp_def, e.apply_symm_apply] using
    congrFun (submatrix_mulVec_equiv P (fun j ↦ x j) e e) (e.symm i)

/-- A literal reindexed finite sum of Kronecker matrices becomes the same
finite sum of continuous tensor actions under the prescribed coordinate
isometry. The isometry first relabels the coordinates and then uses the
inverse product orthonormal basis. The finite family, its index set and its
factor order are unchanged. No spectral assertion is made. -/
theorem toEuclideanCLM_reindexed_kronecker_sum_intertwining
    {𝕜 Z X Y ι : Type*} [RCLike 𝕜]
    [Fintype Z] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq Z] [DecidableEq X] [DecidableEq Y]
    (e : Z ≃ X × Y) (A : ι → Matrix X X 𝕜) (B : ι → Matrix Y Y 𝕜) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e
    let Phi := ((EuclideanSpace.basisFun X 𝕜).tensorProduct
      (EuclideanSpace.basisFun Y 𝕜)).repr
    let T := U.trans Phi.symm
    T.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := 𝕜) (n := Z) ((∑ i, A i ⊗ₖ B i).submatrix e e) =
      (∑ i, TensorProduct.mapL (toEuclideanCLM (𝕜 := 𝕜) (n := X) (A i))
        (toEuclideanCLM (𝕜 := 𝕜) (n := Y) (B i))) ∘L
        T.toContinuousLinearEquiv.toContinuousLinearMap := by
  classical
  intro U Phi T
  let P := ∑ i, A i ⊗ₖ B i
  let K := ∑ i, TensorProduct.mapL (toEuclideanCLM (𝕜 := 𝕜) (n := X) (A i))
    (toEuclideanCLM (𝕜 := 𝕜) (n := Y) (B i))
  have hsum : Phi.toContinuousLinearEquiv.toContinuousLinearMap ∘L K =
      toEuclideanCLM (𝕜 := 𝕜) (n := X × Y) P ∘L
        Phi.toContinuousLinearEquiv.toContinuousLinearMap := by
    dsimp only [K, P]
    rw [ContinuousLinearMap.comp_finsetSum, map_sum,
      ContinuousLinearMap.finsetSum_comp]
    exact Finset.sum_congr rfl fun i _ ↦ toEuclideanCLM_kronecker_intertwining (A i) (B i)
  ext x
  apply Phi.injective
  change Phi (Phi.symm (U (toEuclideanCLM (𝕜 := 𝕜) (n := Z)
      (P.submatrix e e) x))) = Phi (K (Phi.symm (U x)))
  rw [Phi.apply_symm_apply]
  have hleft : U (toEuclideanCLM (𝕜 := 𝕜) (n := Z) (P.submatrix e e) x) =
      toEuclideanCLM (𝕜 := 𝕜) (n := X × Y) P (U x) :=
    congrArg (fun f : EuclideanSpace 𝕜 Z →L[𝕜] EuclideanSpace 𝕜 (X × Y) ↦ f x)
      (toEuclideanCLM_submatrix_intertwining e P)
  have hright : Phi (K (Phi.symm (U x))) =
      toEuclideanCLM (𝕜 := 𝕜) (n := X × Y) P (U x) := by
    have h := congrArg (fun f :
        (EuclideanSpace 𝕜 X ⊗[𝕜] EuclideanSpace 𝕜 Y) →L[𝕜]
          EuclideanSpace 𝕜 (X × Y) ↦ f (Phi.symm (U x))) hsum
    change Phi (K (Phi.symm (U x))) =
      toEuclideanCLM (𝕜 := 𝕜) (n := X × Y) P (Phi (Phi.symm (U x))) at h
    simpa only [Phi.apply_symm_apply] using h
  exact hleft.trans hright.symm

end Matrix

namespace TensorProduct

/-- Exchanging the tensor factors turns a finite intertwining decomposition
into the corresponding decomposition with the factors reversed. Conjugation
by the exchanged coordinate isometry gives that same literal tensor sum.
No completeness, finite-dimensionality or nonvanishing hypothesis is needed. -/
theorem intertwining_sum_mapL_commIsometry
    {𝕜 E L R ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]
    [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [Fintype ι]
    (T : E ≃ₗᵢ[𝕜] L ⊗[𝕜] R) (K : E →L[𝕜] E)
    (A : ι → L →L[𝕜] L) (B : ι → R →L[𝕜] R)
    (h : T.toContinuousLinearEquiv.toContinuousLinearMap ∘L K =
      (∑ i, mapL (A i) (B i)) ∘L T.toContinuousLinearEquiv.toContinuousLinearMap) :
    let Tm := T.trans (commIsometry 𝕜 L R)
    (Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L K =
      (∑ i, mapL (B i) (A i)) ∘L Tm.toContinuousLinearEquiv.toContinuousLinearMap) ∧
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L K ∘L
          Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        ∑ i, mapL (B i) (A i) := by
  intro Tm
  let C := commIsometry 𝕜 L R
  have hswap : C.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (∑ i, mapL (A i) (B i)) =
      (∑ i, mapL (B i) (A i)) ∘L C.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp]
    exact Finset.sum_congr rfl fun i _ ↦ (mapL_comp_commIsometry (B i) (A i)).symm
  have hmiddle : Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L K =
      (∑ i, mapL (B i) (A i)) ∘L Tm.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext x
    change C (T (K x)) = (∑ i, mapL (B i) (A i)) (C (T x))
    have hx : T (K x) = (∑ i, mapL (A i) (B i)) (T x) :=
      congrArg (fun f : E →L[𝕜] L ⊗[𝕜] R ↦ f x) h
    have hs : C ((∑ i, mapL (A i) (B i)) (T x)) =
        (∑ i, mapL (B i) (A i)) (C (T x)) :=
      congrArg (fun f : (L ⊗[𝕜] R) →L[𝕜] R ⊗[𝕜] L ↦ f (T x)) hswap
    exact (congrArg C hx).trans hs
  refine ⟨hmiddle, ?_⟩
  ext y
  have hy := congrArg (fun f : E →L[𝕜] R ⊗[𝕜] L ↦ f (Tm.symm y)) hmiddle
  change Tm (K (Tm.symm y)) =
    (∑ i, mapL (B i) (A i)) (Tm (Tm.symm y)) at hy
  change Tm (K (Tm.symm y)) = (∑ i, mapL (B i) (A i)) y
  simpa only [Tm.apply_symm_apply] using hy

end TensorProduct


section

open Matrix

open scoped BigOperators Kronecker

section

section

open scoped BigOperators Kronecker TensorProduct

namespace Matrix

/-- A literal reindexed Kronecker sum becomes a middle-first conjugated
continuous tensor sum in the standard product coordinates. This combines
the existing coordinate and tensor-swap identities, independently of any
physical operator. Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
    {Z X Y ι : Type*} [Fintype Z] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq Z] [DecidableEq X] [DecidableEq Y]
    (e : Z ≃ X × Y) (A : ι → Matrix X X ℂ) (B : ι → Matrix Y Y ℂ)
    (P : Matrix Z Z ℂ) (hP : P = (∑ i, A i ⊗ₖ B i).submatrix e e) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    let Phi := ((EuclideanSpace.basisFun X ℂ).tensorProduct
      (EuclideanSpace.basisFun Y ℂ)).repr
    let T := U.trans Phi.symm
    let Tm := T.trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ X) (EuclideanSpace ℂ Y))
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := ℂ) (n := Z) P ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      ∑ i, TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := Y) (B i))
        (toEuclideanCLM (𝕜 := ℂ) (n := X) (A i)) := by
  intro U Phi T Tm
  have hT : T.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      toEuclideanCLM (𝕜 := ℂ) (n := Z) P =
        (∑ i, TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := X) (A i))
          (toEuclideanCLM (𝕜 := ℂ) (n := Y) (B i))) ∘L
            T.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [hP]
    exact toEuclideanCLM_reindexed_kronecker_sum_intertwining
      (𝕜 := ℂ) (Z := Z) (X := X) (Y := Y) (ι := ι) e A B
  exact (TensorProduct.intertwining_sum_mapL_commIsometry
    (𝕜 := ℂ) (E := EuclideanSpace ℂ Z)
    (L := EuclideanSpace ℂ X) (R := EuclideanSpace ℂ Y) (ι := ι) T
    (toEuclideanCLM (𝕜 := ℂ) (n := Z) P)
    (fun i ↦ toEuclideanCLM (𝕜 := ℂ) (n := X) (A i))
    (fun i ↦ toEuclideanCLM (𝕜 := ℂ) (n := Y) (B i)) hT).2
end Matrix
end
end
end
