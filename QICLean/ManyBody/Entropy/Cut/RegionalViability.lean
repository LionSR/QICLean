/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.Cut.SubregionCut
import QICLean.Analysis.Subspace.ViableSubspaceCoordinates
import QICLean.Analysis.TensorProduct.MatrixTensorCoordinates
import QICLean.ManyBody.Entropy.Filter.Optimizer

/-!
# Actual tensor coordinates for regional viable spaces

The finite configuration split, followed by the canonical Euclidean tensor
isometry, places the retained region first and its entire exterior second.
The equivalent construction that first places the exterior first agrees
with this map after exchanging the tensor factors.

These coordinate identities support ALVV, arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440, and tensoring, lines 500–523.

It also contains the following results.

* `Entropy.localLift_middleFirst_conjugation`,
  `Entropy.regionTensorCoordinates_conjugation_localLift`: regional operator matrices in tensor
  coordinates.
-/

section RegionalViability

open scoped TensorProduct

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual retained-region/exterior tensor coordinates. Supporting ALVV,
arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
noncomputable def regionTensorCoordinates (q : ℕ) (J : Finset V) :
    EuclideanSpace ℂ (V → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (J → Fin q) ⊗[ℂ] EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) :=
  (regionConfigurationSplit q J).trans (Submodule.euclideanTensorEquiv _ _)

/-- Regional coordinate extension is viability in the actual tensor split.
Supporting ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
lemma isCloseTo_prodExt_region_iff_isViable {q : ℕ} {delta : ℝ}
    (J : Finset V) (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)))
    (G : Submodule ℂ (EuclideanSpace ℂ (V → Fin q))) :
    Submodule.IsCloseTo delta (Submodule.prodExt S ({v // v ∉ J} → Fin q))
      (G.map (regionConfigurationSplit q J).toLinearEquiv.toLinearMap) ↔
    Submodule.IsViable delta S (G.map (regionTensorCoordinates q J).toLinearEquiv.toLinearMap) := by
  rw [Submodule.isCloseTo_prodExt_iff_isViable, ← Submodule.map_comp]
  rfl

/-- The exterior-first construction used by physical improving families is
exactly the retained-region-first canonical tensor split. Supporting ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
lemma regionTensorCoordinates_eq_exteriorFirst (q : ℕ) (J : Finset V) :
    regionTensorCoordinates q J =
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        ((ManyBody.cutEquiv (fun _ : V ↦ Fin q) J).trans (Equiv.prodComm _ _))).trans
          (Submodule.euclideanTensorEquiv ({v // v ∉ J} → Fin q) (J → Fin q))).trans
        (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ ({v // v ∉ J} → Fin q))
          (EuclideanSpace ℂ (J → Fin q))) := by
  apply LinearIsometryEquiv.ext
  intro psi
  apply (Submodule.euclideanTensorEquiv (J → Fin q) ({v // v ∉ J} → Fin q)).symm.injective
  change (Submodule.euclideanTensorEquiv _ _).symm
      (Submodule.euclideanTensorEquiv _ _ (regionConfigurationSplit q J psi)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [LinearIsometryEquiv.trans_apply]
  rw [Submodule.euclideanTensorEquiv_symm_comm]
  ext p
  rfl

end Entropy

end RegionalViability

section RegionalOperatorCoordinates

/-!
## Regional operator matrices in tensor coordinates

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

end RegionalOperatorCoordinates
