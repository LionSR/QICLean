/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.MatrixAux

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt

/-!
# The Frobenius matrix space as a Hilbert space

This file develops the squared Frobenius norm of a finite complex matrix and
identifies the matrix space with the Euclidean space of its entries. The
identification permits finite-dimensional Hilbert-space results to be applied
to matrix superoperators without introducing a second norm on matrices.

## Main declarations

* `Matrix.frobeniusNormSq`: the squared Frobenius norm.
* `Matrix.frobeniusEquivEuclidean`: vectorization as a complex linear
  isometric equivalence.
* `Matrix.frobeniusEuclideanMap`: transport of a matrix superoperator through
  this equivalence.
* `Matrix.frobeniusEuclideanLinearEquiv`: transport of a linear equivalence
  between matrix spaces.
* `Matrix.frobeniusEuclideanMap_comp`: Frobenius transport preserves
  composition.
* `Matrix.hilbertSchmidtOperatorNorm`: the induced Hilbert--Schmidt operator
  norm of a matrix superoperator.
* `Matrix.frobenius_norm_apply_le_hilbertSchmidtOperatorNorm`: its defining
  application bound.

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/ProjectorDefect/WeightedVirtualHilbert.lean`,
`TNLean/MPS/Symmetry/ContinuousFamily/NearbyInjectiveAdjointActions.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open scoped Matrix Matrix.Norms.Frobenius

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ### Frobenius norm squared -/

/-- The squared Frobenius norm of a finite complex matrix. -/
noncomputable def frobeniusNormSq (A : Matrix m n ℂ) : ℝ :=
  ‖A‖ ^ 2

/-! ### Euclidean-space identification -/

/-- Column vectorization is a linear isometry from matrices with the
Frobenius norm to the Euclidean space of their entries. -/
noncomputable def frobeniusEquivEuclidean
    (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (n × m) where
  toFun A := WithLp.toLp 2 A.vec
  invFun x := of fun i j ↦ WithLp.ofLp x (j, i)
  map_add' A B := by
    apply PiLp.ext
    intro ji
    simp
  map_smul' c A := by
    apply PiLp.ext
    intro ji
    simp
  left_inv A := by
    ext i j
    simp
  right_inv x := by
    apply PiLp.ext
    intro ji
    simp
  norm_map' A := by
    change ‖WithLp.toLp 2 A.vec‖ = ‖A‖
    rw [Matrix.frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
    congr 2
    have hvec : WithLp.ofLp (WithLp.toLp 2 A.vec) = A.vec := rfl
    rw [hvec]
    simp only [Matrix.vec]
    calc
      ∑ x : n × m, ‖A x.2 x.1‖ ^ 2 =
          ∑ j : n, ∑ i : m, ‖A i j‖ ^ 2 := by
        simpa only [Finset.univ_product_univ] using
          (Finset.sum_product'
            (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset m))
            (f := fun j i ↦ ‖A i j‖ ^ 2))
      _ = ∑ i : m, ∑ j : n, ‖A i j‖ ^ 2 := Finset.sum_comm
    simp only [Real.rpow_two, pow_two]

@[simp]
theorem frobeniusEquivEuclidean_apply
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobeniusEquivEuclidean m n A = WithLp.toLp 2 A.vec :=
  rfl

@[simp]
theorem frobeniusEquivEuclidean_symm_apply
    {m n : Type*} [Fintype m] [Fintype n]
    (x : EuclideanSpace ℂ (n × m)) (i : m) (j : n) :
    (frobeniusEquivEuclidean m n).symm x i j = WithLp.ofLp x (j, i) :=
  rfl

/-- Under vectorization, the Euclidean inner product is the
Hilbert--Schmidt trace pairing. -/
theorem inner_frobeniusEquivEuclidean
    {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) :
    inner ℂ (frobeniusEquivEuclidean m n A)
      (frobeniusEquivEuclidean m n B) = Matrix.trace (Aᴴ * B) := by
  rw [frobeniusEquivEuclidean_apply, frobeniusEquivEuclidean_apply,
    EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  exact Matrix.star_vec_dotProduct_vec A B

/-- Transport a linear map between matrix spaces to the corresponding
Euclidean spaces of entries. -/
noncomputable def frobeniusEuclideanMap
    {α β : Type*} [Fintype α] [Fintype β]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    EuclideanSpace ℂ (α × α) →ₗ[ℂ] EuclideanSpace ℂ (β × β) :=
  (frobeniusEquivEuclidean β β).toLinearEquiv.toLinearMap.comp
    (E.comp (frobeniusEquivEuclidean α α).symm.toLinearEquiv.toLinearMap)

@[simp]
theorem frobeniusEuclideanMap_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (X : Matrix α α ℂ) :
    frobeniusEuclideanMap E (frobeniusEquivEuclidean α α X) =
      frobeniusEquivEuclidean β β (E X) := by
  change frobeniusEquivEuclidean β β
      (E ((frobeniusEquivEuclidean α α).symm
        (frobeniusEquivEuclidean α α X))) =
    frobeniusEquivEuclidean β β (E X)
  rw [(frobeniusEquivEuclidean α α).symm_apply_apply]

/-! ### Hilbert--Schmidt operator norm -/

/-- The Hilbert--Schmidt `2 → 2` operator norm of a matrix superoperator,
transported through column vectorization. -/
noncomputable def hilbertSchmidtOperatorNorm
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (frobeniusEuclideanMap S)‖

/-- The defining application bound for the Hilbert--Schmidt `2 → 2`
operator norm. -/
theorem frobenius_norm_apply_le_hilbertSchmidtOperatorNorm
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (X : Matrix α α ℂ) :
    ‖S X‖ ≤ hilbertSchmidtOperatorNorm S * ‖X‖ := by
  have h := (LinearMap.toContinuousLinearMap (frobeniusEuclideanMap S)).le_opNorm
    (frobeniusEquivEuclidean α α X)
  simpa only [hilbertSchmidtOperatorNorm, frobeniusEuclideanMap_apply,
    LinearMap.coe_toContinuousLinearMap', LinearIsometryEquiv.norm_map] using h

/-- Transport a linear equivalence between finite matrix spaces through
Frobenius vectorization. -/
noncomputable def frobeniusEuclideanLinearEquiv
    {α β : Type*} [Fintype α] [Fintype β]
    (E : Matrix α α ℂ ≃ₗ[ℂ] Matrix β β ℂ) :
    EuclideanSpace ℂ (α × α) ≃ₗ[ℂ] EuclideanSpace ℂ (β × β) :=
  (frobeniusEquivEuclidean α α).toLinearEquiv.symm.trans
    (E.trans (frobeniusEquivEuclidean β β).toLinearEquiv)

/-- Frobenius transport of a linear equivalence agrees with its action on a
vectorized matrix. -/
@[simp]
theorem frobeniusEuclideanLinearEquiv_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (E : Matrix α α ℂ ≃ₗ[ℂ] Matrix β β ℂ) (X : Matrix α α ℂ) :
    frobeniusEuclideanLinearEquiv E (frobeniusEquivEuclidean α α X) =
      frobeniusEquivEuclidean β β (E X) := by
  change frobeniusEquivEuclidean β β
      (E ((frobeniusEquivEuclidean α α).symm
        (frobeniusEquivEuclidean α α X))) =
    frobeniusEquivEuclidean β β (E X)
  rw [(frobeniusEquivEuclidean α α).symm_apply_apply]

/-- Frobenius transport preserves composition of linear maps between matrix
spaces. -/
@[simp]
theorem frobeniusEuclideanMap_comp
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (F : Matrix β β ℂ →ₗ[ℂ] Matrix γ γ ℂ) :
    frobeniusEuclideanMap (F.comp E) =
      (frobeniusEuclideanMap F).comp (frobeniusEuclideanMap E) := by
  apply LinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (frobeniusEquivEuclidean α α).surjective x
  change frobeniusEuclideanMap (F.comp E)
      (frobeniusEquivEuclidean α α X) =
    frobeniusEuclideanMap F
      (frobeniusEuclideanMap E (frobeniusEquivEuclidean α α X))
  rw [frobeniusEuclideanMap_apply, frobeniusEuclideanMap_apply,
    frobeniusEuclideanMap_apply, LinearMap.comp_apply]

/-- For a matrix endomorphism, Frobenius transport is conjugation by the
vectorization equivalence. -/
theorem frobeniusEuclideanMap_eq_conj
    {α : Type*} [Fintype α]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    frobeniusEuclideanMap E =
      (frobeniusEquivEuclidean α α).toLinearEquiv.conj E := by
  rfl

/-- Frobenius transport carries conjugation by a matrix-space equivalence to
conjugation by the transported Euclidean-space equivalence. -/
theorem frobeniusEuclideanMap_conj
    {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℂ ≃ₗ[ℂ] Matrix β β ℂ)
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ) :
    frobeniusEuclideanMap (S.conj E) =
      (frobeniusEuclideanLinearEquiv S).conj (frobeniusEuclideanMap E) := by
  rfl

end Matrix

section

open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.Frobenius

macro "weighted_matrix_instances " ρ:term:max ppSpace hρ:term:max " in" ppLine
    body:term : term =>
  `(letI : NormedAddCommGroup _ := Matrix.toMatrixNormedAddCommGroup $ρ $hρ
    letI : SeminormedAddCommGroup _ :=
      (Matrix.toMatrixNormedAddCommGroup $ρ $hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ _ := Matrix.toMatrixInnerProductSpace $ρ ($hρ).posSemidef
    $body)

macro "weighted_matrix_instances " ρ:term:max ppSpace hρ:term:max : tactic =>
  `(tactic|
    (let : NormedAddCommGroup _ := Matrix.toMatrixNormedAddCommGroup $ρ $hρ
     let : SeminormedAddCommGroup _ :=
       (Matrix.toMatrixNormedAddCommGroup $ρ $hρ).toSeminormedAddCommGroup
     let : InnerProductSpace ℂ _ := Matrix.toMatrixInnerProductSpace $ρ ($hρ).posSemidef))

macro "weighted_matrix_norm_instances " ρ:term:max ppSpace hρ:term:max " in" ppLine
    body:term : term =>
  `(weighted_matrix_instances $ρ $hρ in
    letI : Norm _ := (Matrix.toMatrixNormedAddCommGroup $ρ $hρ).toNorm
    $body)

macro "weighted_matrix_norm_instances " ρ:term:max ppSpace hρ:term:max : tactic =>
  `(tactic|
    (weighted_matrix_instances $ρ $hρ
     let : Norm _ := (Matrix.toMatrixNormedAddCommGroup $ρ $hρ).toNorm))

namespace Matrix

noncomputable section

private noncomputable def frobeniusLinearEquiv (D : ℕ) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv

/-- Mathlib's weighted matrix inner product agrees, by cyclicity of the trace,
with the convention \(\operatorname{Tr}(\rho X^\dagger Y)\) in FNW 1992, equation (5.6). -/
theorem rhoWeighted_inner {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : ρ.PosDef) (X Y : Matrix (Fin D) (Fin D) ℂ) :
    weighted_matrix_norm_instances ρ hρ in
    inner ℂ X Y = Matrix.trace (ρ * Xᴴ * Y) := by
  weighted_matrix_norm_instances ρ hρ
  change Matrix.trace (Y * ρ * Xᴴ) = Matrix.trace (ρ * Xᴴ * Y)
  exact (Matrix.trace_mul_cycle ρ Xᴴ Y).symm

/-- The squared weighted norm is the real part of \(\operatorname{Tr}(\rho X^\dagger X)\). -/
theorem rhoWeighted_norm_sq {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : ρ.PosDef) (X : Matrix (Fin D) (Fin D) ℂ) :
    weighted_matrix_norm_instances ρ hρ in
    ‖X‖ ^ 2 = (Matrix.trace (ρ * Xᴴ * X)).re := by
  weighted_matrix_norm_instances ρ hρ
  calc
    ‖X‖ ^ 2 = (inner ℂ X X).re := (inner_self_eq_norm_sq (𝕜 := ℂ) X).symm
    _ = (Matrix.trace (ρ * Xᴴ * X)).re :=
      congrArg Complex.re (rhoWeighted_inner ρ hρ X X)

private theorem inner_rightMul_cfcSqrt
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    weighted_matrix_norm_instances ρ hρ in
    inner ℂ (frobeniusLinearEquiv D (X * CFC.sqrt ρ))
        (frobeniusLinearEquiv D (Y * CFC.sqrt ρ)) = inner ℂ X Y := by
  weighted_matrix_norm_instances ρ hρ
  rw [show inner ℂ (frobeniusLinearEquiv D (X * CFC.sqrt ρ))
      (frobeniusLinearEquiv D (Y * CFC.sqrt ρ)) =
        Matrix.trace ((X * CFC.sqrt ρ)ᴴ * (Y * CFC.sqrt ρ)) from
      Matrix.inner_frobeniusEquivEuclidean _ _, rhoWeighted_inner ρ hρ]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_cfc_sqrt]
  calc
    Matrix.trace (CFC.sqrt ρ * Xᴴ * (Y * CFC.sqrt ρ)) =
        Matrix.trace (CFC.sqrt ρ * (Xᴴ * Y) * CFC.sqrt ρ) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (CFC.sqrt ρ * CFC.sqrt ρ * (Xᴴ * Y)) :=
      Matrix.trace_mul_cycle (CFC.sqrt ρ) (Xᴴ * Y) (CFC.sqrt ρ)
    _ = Matrix.trace (ρ * Xᴴ * Y) := by
      rw [CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
      simp only [Matrix.mul_assoc]

/-- Right multiplication by \(\sqrt{\rho}\), followed by Frobenius vectorization,
is a complex linear isometric equivalence from the \(\rho\)-weighted matrix space
to the Euclidean space of its entries. -/
noncomputable def rhoWeightedEquivEuclidean
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    weighted_matrix_norm_instances ρ hρ in
    Matrix (Fin D) (Fin D) ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D × Fin D) := by
  weighted_matrix_norm_instances ρ hρ
  exact {
    toFun X := frobeniusLinearEquiv D (X * CFC.sqrt ρ)
    invFun x := (frobeniusLinearEquiv D).symm x * (CFC.sqrt ρ)⁻¹
    map_add' X Y := by
      rw [Matrix.add_mul, map_add]
    map_smul' c X := by
      rw [Matrix.smul_mul, map_smul]
      rfl
    left_inv X := by
      change (frobeniusLinearEquiv D).symm
          (frobeniusLinearEquiv D (X * CFC.sqrt ρ)) * (CFC.sqrt ρ)⁻¹ = X
      rw [(frobeniusLinearEquiv D).symm_apply_apply, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hρ.isUnit_det_cfc_sqrt, Matrix.mul_one]
    right_inv x := by
      change frobeniusLinearEquiv D
          (((frobeniusLinearEquiv D).symm x * (CFC.sqrt ρ)⁻¹) * CFC.sqrt ρ) = x
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ.isUnit_det_cfc_sqrt, Matrix.mul_one,
        (frobeniusLinearEquiv D).apply_symm_apply]
    norm_map' X := by
      have hsquare : ‖frobeniusLinearEquiv D (X * CFC.sqrt ρ)‖ ^ 2 = ‖X‖ ^ 2 := by
        calc
          ‖frobeniusLinearEquiv D (X * CFC.sqrt ρ)‖ ^ 2 =
              (inner ℂ (frobeniusLinearEquiv D (X * CFC.sqrt ρ))
                (frobeniusLinearEquiv D (X * CFC.sqrt ρ))).re :=
            (inner_self_eq_norm_sq (𝕜 := ℂ)
              (frobeniusLinearEquiv D (X * CFC.sqrt ρ))).symm
          _ = (inner ℂ X X).re :=
            congrArg Complex.re (inner_rightMul_cfcSqrt ρ hρ X X)
          _ = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
      change ‖frobeniusLinearEquiv D (X * CFC.sqrt ρ)‖ = ‖X‖
      nlinarith [norm_nonneg (frobeniusLinearEquiv D (X * CFC.sqrt ρ)), norm_nonneg X]
  }

/-- The weighted Euclidean equivalence sends \(X\) to the Frobenius vectorization
of \(X\sqrt{\rho}\). -/
@[simp]
theorem rhoWeightedEquivEuclidean_apply
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    weighted_matrix_norm_instances ρ hρ in
    rhoWeightedEquivEuclidean ρ hρ X =
      WithLp.toLp 2 (X * CFC.sqrt ρ).vec := by
  weighted_matrix_norm_instances ρ hρ
  rfl

/-- The inverse weighted Euclidean equivalence applies inverse Frobenius
vectorization and then multiplies on the right by \((\sqrt{\rho})^{-1}\). -/
@[simp]
theorem rhoWeightedEquivEuclidean_symm_apply
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    weighted_matrix_norm_instances ρ hρ in
    (rhoWeightedEquivEuclidean ρ hρ).symm x =
      Matrix.of (fun i j => WithLp.ofLp x (j, i)) * (CFC.sqrt ρ)⁻¹ := by
  weighted_matrix_norm_instances ρ hρ
  rfl

end

end Matrix

end

section

open scoped Matrix Matrix.Norms.Frobenius

open Filter Topology

namespace Matrix

/-- Bond conjugation acting on the Euclidean space of matrix entries. -/
noncomputable def conjugationEuclideanCLM {D : ℕ} (V : Matrix (Fin D) (Fin D) ℂ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (frobeniusEuclideanMap ((LinearMap.mulRight ℂ Vᴴ).comp
    (LinearMap.mulLeft ℂ V))).toContinuousLinearMap

/-- Euclidean bond conjugation agrees with ordinary matrix conjugation. -/
theorem conjugationEuclideanCLM_apply {D : ℕ}
    (V X : Matrix (Fin D) (Fin D) ℂ) :
    conjugationEuclideanCLM V (frobeniusEquivEuclidean (Fin D) (Fin D) X) =
      frobeniusEquivEuclidean (Fin D) (Fin D) (V * X * Vᴴ) := by
  simp only [conjugationEuclideanCLM, LinearMap.coe_toContinuousLinearMap',
    frobeniusEuclideanMap_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply]

end Matrix

end
