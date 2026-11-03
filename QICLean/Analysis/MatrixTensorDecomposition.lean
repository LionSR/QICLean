/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixTensorCoordinates
import QICLean.Analysis.InvariantOperatorBounds

/-!
# Recovering the same global matrix from a tensor decomposition

The canonical middle-first tensor identity is equivalent to the literal
whole-matrix Kronecker identity. This permits changing retained regions
without replacing the actual global operator. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7 and Lemma l:er,
lines 597–622 and 1332–1333.
-/

open scoped BigOperators Kronecker TensorProduct
namespace Matrix

/-- The canonical middle-first tensor decomposition is equivalent to the
whole-matrix decomposition with the exterior factor first. Both identities
represent the same supplied matrix. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem toEuclideanCLM_middleFirst_conjugation_eq_sum_iff
    {Z X Y ι : Type*} [Fintype Z] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq Z] [DecidableEq X] [DecidableEq Y]
    (e : Z ≃ X × Y) (A : ι → Matrix X X ℂ) (B : ι → Matrix Y Y ℂ)
    (P : Matrix Z Z ℂ) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    let Phi := ((EuclideanSpace.basisFun X ℂ).tensorProduct
      (EuclideanSpace.basisFun Y ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ X) (EuclideanSpace ℂ Y))
    (Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := ℂ) (n := Z) P ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      ∑ i, TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := Y) (B i))
        (toEuclideanCLM (𝕜 := ℂ) (n := X) (A i))) ↔
      P = (∑ i, A i ⊗ₖ B i).submatrix e e := by
  intro U Phi Tm
  constructor
  · intro h
    apply (toEuclideanCLM (𝕜 := ℂ) (n := Z)).injective
    apply Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.injective
    exact h.trans (toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
      e A B ((∑ i, A i ⊗ₖ B i).submatrix e e) rfl).symm
  · intro h
    exact toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum e A B P h

/-- Pull back the same tensor-decomposed filter to its whole-space matrix
and target. The coefficients are the actual matrices of the supplied
exterior maps. This derives the original matrix decomposition and all four
operator bounds, without selecting another filter. Supporting ALVV,
arXiv:1602.08828v2, Lemma l:er and Proposition 5.7, lines 597–622 and 1332–1333. -/
theorem global_filter_of_middleFirst_tensor_decomposition
    {Z X Y ι : Type*} [Fintype Z] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq Z] [DecidableEq X] [DecidableEq Y]
    (e : Z ≃ X × Y) (W : ι → Matrix Y Y ℂ)
    (K0 : EuclideanSpace ℂ Y ⊗[ℂ] EuclideanSpace ℂ X →L[ℂ]
      EuclideanSpace ℂ Y ⊗[ℂ] EuclideanSpace ℂ X)
    (Rop : ι → EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X)
    (T : Submodule ℂ (EuclideanSpace ℂ Z)) (Delta : ℝ) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    let Phi := ((EuclideanSpace.basisFun X ℂ).tensorProduct
      (EuclideanSpace.basisFun Y ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ X) (EuclideanSpace ℂ Y))
    let Tc := T.map Tm.toLinearEquiv.toLinearMap
    K0 = ∑ i, TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := Y) (W i)) (Rop i) →
    (∀ t ∈ Tc, K0 t ∈ Tc) → (∀ z ∈ Tcᗮ, K0 z ∈ Tcᗮ) →
    (∀ t ∈ Tc, ‖t‖ ≤ ‖K0 t‖) →
    (∀ z ∈ Tcᗮ, ‖K0 z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) →
    let K := Tm.symm.toContinuousLinearEquiv.conjContinuousAlgEquiv K0
    let M := fun i ↦ (toEuclideanCLM (𝕜 := ℂ) (n := X)).symm (Rop i)
    let P := (toEuclideanCLM (𝕜 := ℂ) (n := Z)).symm K
    P = (∑ i, M i ⊗ₖ W i).submatrix e e ∧
    (∀ t ∈ T, K t ∈ T) ∧ (∀ z ∈ Tᗮ, K z ∈ Tᗮ) ∧
    (∀ t ∈ T, ‖t‖ ≤ ‖K t‖) ∧
    (∀ z ∈ Tᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) := by
  intro U Phi Tm Tc hdec hKT hKTo hlow hhigh K M P
  have hp : toEuclideanCLM (𝕜 := ℂ) (n := Z) P = K :=
    (toEuclideanCLM (𝕜 := ℂ) (n := Z)).apply_symm_apply K
  have hconj : Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv
      (toEuclideanCLM (𝕜 := ℂ) (n := Z) P) = K0 := by
    rw [hp]
    exact Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.apply_symm_apply K0
  have hmatrix : P = (∑ i, M i ⊗ₖ W i).submatrix e e := by
    apply (toEuclideanCLM_middleFirst_conjugation_eq_sum_iff e M W P).mp
    change Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv
      (toEuclideanCLM (𝕜 := ℂ) (n := Z) P) = _
    simpa only [M, StarAlgEquiv.apply_symm_apply] using hconj.trans hdec
  have hT : Tc.map Tm.symm.toLinearEquiv.toLinearMap = T :=
    (Submodule.map_symm_eq_iff Tm.toLinearEquiv).mpr rfl
  let Props := fun S : Submodule ℂ (EuclideanSpace ℂ Z) ↦
    (∀ t ∈ S, K t ∈ S) ∧ (∀ z ∈ Sᗮ, K z ∈ Sᗮ) ∧
    (∀ t ∈ S, ‖t‖ ≤ ‖K t‖) ∧
    (∀ z ∈ Sᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2)
  have hback : Props (Tc.map Tm.symm.toLinearEquiv.toLinearMap) :=
    ContinuousLinearMap.invariant_subspace_bounds_conj Tm.symm K0 Tc Delta
      hKT hKTo hlow hhigh
  exact ⟨hmatrix, Eq.mp (congrArg Props hT) hback⟩

end Matrix
