/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixTensorCoordinates
import QICLean.Entropy.RegionUnion
import QICLean.Entropy.RegionalViability

/-!
# Regional operator matrices in tensor coordinates

The identity extension of an actual regional matrix becomes its tensor
product with the environmental identity in the canonical regional tensor
coordinates. Empty regions and zero local dimensions are included.
This is finite-dimensional coordinate algebra supporting ALVV,
arXiv:1602.08828v2, Definition `d:vs`, lines 433–440, and the tensor
factor argument in Lemma `l:er`, lines 606–622.
-/

open Matrix
open scoped BigOperators Kronecker TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

namespace Entropy

private theorem localLift_eq_middleFirst {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (J : Finset V)
    (K : Matrix (J → Fin q) (J → Fin q) ℂ) :
    let tau := (ManyBody.cutEquiv (fun _ : V ↦ Fin q) J).trans
      (Equiv.prodComm _ _)
    ManyBody.place (X := fun _ ↦ Fin q) J K =
      ((1 : Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ) ⊗ₖ K).submatrix tau tau := by
  classical
  intro tau
  ext σ ρ
  rw [ManyBody.place_apply]
  simp only [submatrix_apply, kroneckerMap_apply, one_apply,
    tau, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  have hfst (ξ : V → Fin q) :
      ((ManyBody.cutEquiv (fun _ : V ↦ Fin q) J) ξ).1 = (fun v : J ↦ ξ v) := rfl
  have hsnd (ξ : V → Fin q) :
      ((ManyBody.cutEquiv (fun _ : V ↦ Fin q) J) ξ).2 =
        (fun v : {v // v ∉ J} ↦ ξ v) := rfl
  have hrest : ((fun v : {v // v ∉ J} ↦ σ v) = (fun v : {v // v ∉ J} ↦ ρ v)) ↔
      ∀ v ∉ J, σ v = ρ v := by
    constructor
    · intro heq v hv
      exact congrFun heq ⟨v, hv⟩
    · intro heq
      funext v
      exact heq v v.property
  simp only [hfst, hsnd, hrest, ite_mul, one_mul, zero_mul]

/-- Identity extension becomes a tensor factor in the explicit
exterior-first product coordinates followed by tensor exchange. This
is the same regional identity in a second standard coordinate form.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333,
and the tensor factor argument in Lemma `l:er`, lines 606–622. -/
theorem localLift_middleFirst_conjugation {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (J : Finset V)
    (K : Matrix (J → Fin q) (J → Fin q) ℂ) :
    let beta := fun _ : V ↦ Fin q
    let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
      (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
      (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := ℂ) (n := V → Fin q)
          (ManyBody.place (X := fun _ ↦ Fin q) J K) ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) K)
        (1 : EuclideanSpace ℂ ({v // v ∉ J} → Fin q) →L[ℂ]
          EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) := by
  intro beta tau U Phi Tm
  have hmatrix : ManyBody.place (X := fun _ ↦ Fin q) J K =
      (∑ _i : Unit, (1 : Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ) ⊗ₖ K).submatrix
        tau tau := by
    simpa only [Fintype.sum_unique] using localLift_eq_middleFirst J K
  have hconj := toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
    tau (fun _ : Unit ↦ (1 : Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ))
    (fun _ : Unit ↦ K) (ManyBody.place (X := fun _ ↦ Fin q) J K) hmatrix
  simpa only [Fintype.sum_unique, map_one] using hconj

/-- Identity extension becomes the regional tensor factor times the
identity on its full environment, in the actual canonical coordinates.
Auxiliary to ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440,
and Lemma `l:er`, lines 606–622. No positivity or nonzero-dimension
hypothesis is imposed. -/
theorem regionTensorCoordinates_conjugation_localLift
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (J : Finset V)
    (K : Matrix (J → Fin q) (J → Fin q) ℂ) :
    let Tm := regionTensorCoordinates q J
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := ℂ) (n := V → Fin q)
          (ManyBody.place (X := fun _ ↦ Fin q) J K) ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) K)
        (1 : EuclideanSpace ℂ ({v // v ∉ J} → Fin q) →L[ℂ]
          EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) := by
  intro Tm
  dsimp only [Tm]
  rw [regionTensorCoordinates_eq_exteriorFirst]
  exact localLift_middleFirst_conjugation J K

end Entropy
