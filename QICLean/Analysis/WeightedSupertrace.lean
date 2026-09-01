/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FrobeniusHilbert
import QICLean.Algebra.MatrixTracePairing
import QICLean.Analysis.MatrixSqrt

import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Weighted superoperator trace bound

This file bounds the algebraic trace pairing of a linear map with a two-sided
matrix multiplier on the Hilbert space induced by a positive-definite weight.
The estimate is dimension-free apart from the exact weight factor
`(Matrix.trace ρ⁻¹).re`.

## Main result

* `Matrix.norm_trace_comp_twoSidedMul_le_weighted` bounds the operator trace of
  `F.comp (X ↦ Bᴴ * X * C)` by the weighted operator norm of `F` and the
  weighted norms of `B` and `C`.
-/

open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.Frobenius

namespace Matrix

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

noncomputable section

private noncomputable def frobeniusLinearEquiv
    (n : Type*) [Fintype n] :
    Matrix n n ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (n × n) :=
  (frobeniusEquivEuclidean n n).toLinearEquiv

private noncomputable def entryL2Norm
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  √(∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ))

private theorem inner_frobeniusLinearEquiv
    {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    inner ℂ (frobeniusLinearEquiv n X) (frobeniusLinearEquiv n Y) =
      Matrix.trace (Xᴴ * Y) :=
  inner_frobeniusEquivEuclidean X Y

private theorem norm_frobeniusLinearEquiv_eq_entryL2Norm
    {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    ‖frobeniusLinearEquiv n X‖ = entryL2Norm X := by
  rw [PiLp.norm_eq_of_L2, entryL2Norm]
  change √(∑ p : n × n, ‖X p.2 p.1‖ ^ (2 : ℕ)) =
    √(∑ i, ∑ j, ‖X i j‖ ^ (2 : ℕ))
  rw [Fintype.sum_prod_type, Finset.sum_comm]

private theorem entryL2Norm_eq_frobenius_norm
    {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    entryL2Norm X = ‖X‖ := by
  rw [← norm_frobeniusLinearEquiv_eq_entryL2Norm]
  exact (frobeniusEquivEuclidean n n).norm_map X

private noncomputable def weightedLinearEquiv
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef) :
    Matrix n n ℂ ≃ₗ[ℂ] Matrix n n ℂ :=
  let s := CFC.sqrt ρ
  {
    toFun X := X * s
    invFun X := X * s⁻¹
    map_add' X Y := Matrix.add_mul X Y s
    map_smul' c X := by
      rw [Matrix.smul_mul]
      rfl
    left_inv X := by
      change (X * s) * s⁻¹ = X
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρ.isUnit_det_cfc_sqrt,
        Matrix.mul_one]
    right_inv X := by
      change (X * s⁻¹) * s = X
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ.isUnit_det_cfc_sqrt,
        Matrix.mul_one]
  }

private noncomputable def weightedEquivEuclidean
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef) :
    letI : NormedAddCommGroup (Matrix n n ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix n n ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm (Matrix n n ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    Matrix n n ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (n × n) := by
  letI : NormedAddCommGroup (Matrix n n ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  letI : SeminormedAddCommGroup (Matrix n n ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  letI : Norm (Matrix n n ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let s := CFC.sqrt ρ
  exact {
    toFun X := frobeniusLinearEquiv n (X * s)
    invFun x := (frobeniusLinearEquiv n).symm x * s⁻¹
    map_add' X Y := by
      rw [Matrix.add_mul, map_add]
    map_smul' c X := by
      rw [Matrix.smul_mul, map_smul]
      rfl
    left_inv X := by
      change (frobeniusLinearEquiv n).symm
          (frobeniusLinearEquiv n (X * s)) * s⁻¹ = X
      rw [(frobeniusLinearEquiv n).symm_apply_apply, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hρ.isUnit_det_cfc_sqrt, Matrix.mul_one]
    right_inv x := by
      change frobeniusLinearEquiv n
          (((frobeniusLinearEquiv n).symm x * s⁻¹) * s) = x
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ.isUnit_det_cfc_sqrt,
        Matrix.mul_one, (frobeniusLinearEquiv n).apply_symm_apply]
    norm_map' X := by
      have hsquare : ‖frobeniusLinearEquiv n (X * s)‖ ^ 2 = ‖X‖ ^ 2 := by
        calc
          ‖frobeniusLinearEquiv n (X * s)‖ ^ 2 =
              (inner ℂ (frobeniusLinearEquiv n (X * s))
                (frobeniusLinearEquiv n (X * s))).re :=
            (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
          _ = (inner ℂ X X).re := by
            rw [inner_frobeniusLinearEquiv]
            change (Matrix.trace ((X * s)ᴴ * (X * s))).re =
              (Matrix.trace (X * ρ * Xᴴ)).re
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_cfc_sqrt]
            congr 1
            calc
              Matrix.trace (s * Xᴴ * (X * s)) =
                  Matrix.trace (s * (Xᴴ * X) * s) := by
                simp only [Matrix.mul_assoc]
              _ = Matrix.trace (s * s * (Xᴴ * X)) :=
                Matrix.trace_mul_cycle s (Xᴴ * X) s
              _ = Matrix.trace (ρ * Xᴴ * X) := by
                rw [CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
                simp only [Matrix.mul_assoc]
              _ = Matrix.trace (X * ρ * Xᴴ) := Matrix.trace_mul_cycle ρ Xᴴ X
          _ = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
      change ‖frobeniusLinearEquiv n (X * s)‖ = ‖X‖
      nlinarith [norm_nonneg (frobeniusLinearEquiv n (X * s)), norm_nonneg X]
  }

open scoped Classical in
private theorem entryL2Norm_mul_sqrt_eq_weighted_norm
    {n : Type*} [Fintype n]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef) (X : Matrix n n ℂ) :
    letI : NormedAddCommGroup (Matrix n n ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix n n ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm (Matrix n n ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    entryL2Norm (X * CFC.sqrt ρ) = ‖X‖ := by
  classical
  let : NormedAddCommGroup (Matrix n n ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix n n ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix n n ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm (Matrix n n ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have h := (weightedEquivEuclidean ρ hρ).norm_map X
  change ‖frobeniusLinearEquiv n (X * CFC.sqrt ρ)‖ = ‖X‖ at h
  rwa [norm_frobeniusLinearEquiv_eq_entryL2Norm] at h

private theorem entryL2Norm_inv_sqrt_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef) :
    entryL2Norm (CFC.sqrt ρ)⁻¹ ^ (2 : ℕ) = (Matrix.trace ρ⁻¹).re := by
  let s := CFC.sqrt ρ
  rw [entryL2Norm_eq_frobenius_norm,
    ← Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
  congr 2
  calc
    s⁻¹ᴴ * s⁻¹ = s⁻¹ * s⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_cfc_sqrt]
    _ = (s * s)⁻¹ := (Matrix.mul_inv_rev s s).symm
    _ = ρ⁻¹ := by rw [CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]

private theorem norm_trace_conjTranspose_mul_le_entryL2Norm
    {m n : Type*} [Fintype m] [Fintype n]
    (P Q : Matrix m n ℂ) :
    ‖Matrix.trace (Pᴴ * Q)‖ ≤ entryL2Norm P * entryL2Norm Q := by
  let S := ∑ p : m × n, ‖P p.1 p.2‖ * ‖Q p.1 p.2‖
  have hnorm : ‖Matrix.trace (Pᴴ * Q)‖ ≤ S := by
    calc
      ‖Matrix.trace (Pᴴ * Q)‖ =
          ‖∑ j : n, ∑ i : m, star (P i j) * Q i j‖ := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.conjTranspose_apply]
      _ ≤ ∑ j : n, ∑ i : m, ‖star (P i j) * Q i j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ norm_sum_le _ _)
      _ = ∑ j : n, ∑ i : m, ‖P i j‖ * ‖Q i j‖ := by
        simp only [norm_mul, norm_star]
      _ = S := by
        dsimp only [S]
        rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hPnonneg : 0 ≤ ∑ i, ∑ j, ‖P i j‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hQnonneg : 0 ≤ ∑ i, ∑ j, ‖Q i j‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hSsq : S ^ (2 : ℕ) ≤
      (∑ i, ∑ j, ‖P i j‖ ^ (2 : ℕ)) *
        ∑ i, ∑ j, ‖Q i j‖ ^ (2 : ℕ) := by
    dsimp only [S]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : m × n ↦ ‖P p.1 p.2‖) (fun p : m × n ↦ ‖Q p.1 p.2‖)
    simpa only [Finset.mem_univ, ↓reduceIte, Fintype.sum_prod_type] using h
  calc
    ‖Matrix.trace (Pᴴ * Q)‖ ≤ S := hnorm
    _ ≤ entryL2Norm P * entryL2Norm Q := by
      rw [entryL2Norm, entryL2Norm,
        ← sq_le_sq₀ hSnonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), mul_pow,
        Real.sq_sqrt hPnonneg, Real.sq_sqrt hQnonneg]
      exact hSsq

private theorem entryL2Norm_transpose
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    entryL2Norm Aᵀ = entryL2Norm A := by
  rw [entryL2Norm, entryL2Norm]
  congr 1
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private def twoSidedTraceLeftFactor
    {D : ℕ} (P E : Matrix (Fin D) (Fin D) ℂ) (a d : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun i j ↦ P i a * E d j

private def twoSidedTraceRightFactor
    {D : ℕ} (P A : Matrix (Fin D) (Fin D) ℂ) (a d : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun i j ↦ A i a * star (P j d)

private theorem twoSided_apply_single_factorization
    {D : ℕ} (P A E : Matrix (Fin D) (Fin D) ℂ) (b c : Fin D) :
    (P * Aᴴ) * (Matrix.single b c 1 * (P * E)) =
      ∑ a, ∑ d, (star (A b a) * P c d) •
        twoSidedTraceLeftFactor P E a d := by
  classical
  ext i j
  have hcoord :
      (∑ d, (∑ a, P i a * star (A b a)) * (P c d * E d j)) =
        ∑ a, ∑ d, (star (A b a) * P c d) * (P i a * E d j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr with a
    congr with d
    ring
  simpa [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ite_and, Finset.mul_sum,
    twoSidedTraceLeftFactor] using hcoord

private noncomputable def columnL2Norm
    {m n : Type*} [Fintype m] (A : Matrix m n ℂ) (j : n) : ℝ :=
  √(∑ i, ‖A i j‖ ^ (2 : ℕ))

private noncomputable def rowL2Norm
    {m n : Type*} [Fintype n] (A : Matrix m n ℂ) (i : m) : ℝ :=
  √(∑ j, ‖A i j‖ ^ (2 : ℕ))

private theorem entryL2Norm_twoSidedTraceLeftFactor
    {D : ℕ} (P E : Matrix (Fin D) (Fin D) ℂ) (a d : Fin D) :
    entryL2Norm (twoSidedTraceLeftFactor P E a d) =
      columnL2Norm P a * rowL2Norm E d := by
  have hP : 0 ≤ ∑ i, ‖P i a‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [entryL2Norm, columnL2Norm, rowL2Norm]
  have hmass :
      (∑ i, ∑ j, ‖twoSidedTraceLeftFactor P E a d i j‖ ^ (2 : ℕ)) =
        (∑ i, ‖P i a‖ ^ (2 : ℕ)) * ∑ j, ‖E d j‖ ^ (2 : ℕ) := by
    simp only [twoSidedTraceLeftFactor, norm_mul, mul_pow]
    simp_rw [← Finset.mul_sum]
    simp only [Finset.sum_mul]
  rw [hmass, Real.sqrt_mul hP]

private theorem entryL2Norm_twoSidedTraceRightFactor
    {D : ℕ} (P A : Matrix (Fin D) (Fin D) ℂ) (a d : Fin D) :
    entryL2Norm (twoSidedTraceRightFactor P A a d) =
      columnL2Norm A a * columnL2Norm P d := by
  have hA : 0 ≤ ∑ i, ‖A i a‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [entryL2Norm, columnL2Norm, columnL2Norm]
  have hmass :
      (∑ i, ∑ j, ‖twoSidedTraceRightFactor P A a d i j‖ ^ (2 : ℕ)) =
        (∑ i, ‖A i a‖ ^ (2 : ℕ)) * ∑ j, ‖P j d‖ ^ (2 : ℕ) := by
    simp only [twoSidedTraceRightFactor, norm_mul, norm_star, mul_pow]
    simp_rw [← Finset.mul_sum]
    simp only [Finset.sum_mul]
  rw [hmass, Real.sqrt_mul hA]

private theorem sum_mul_le_sqrt_sum_sq_mul_sqrt_sum_sq
    {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ √(∑ i, f i ^ (2 : ℕ)) * √(∑ i, g i ^ (2 : ℕ)) := by
  let S := ∑ i, f i * g i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hf i) (hg i)
  have hf2 : 0 ≤ ∑ i, f i ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hg2 : 0 ≤ ∑ i, g i ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  rw [← sq_le_sq₀ hS
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), mul_pow,
    Real.sq_sqrt hf2, Real.sq_sqrt hg2]
  simpa only [S, Finset.mem_univ, ↓reduceIte] using h

private theorem sum_columnL2Norm_mul_columnL2Norm_le
    {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) :
    ∑ j, columnL2Norm A j * columnL2Norm B j ≤
      entryL2Norm A * entryL2Norm B := by
  have h := sum_mul_le_sqrt_sum_sq_mul_sqrt_sum_sq
    (fun j ↦ columnL2Norm A j) (fun j ↦ columnL2Norm B j)
    (fun _ ↦ Real.sqrt_nonneg _) (fun _ ↦ Real.sqrt_nonneg _)
  have hA : ∀ j, 0 ≤ ∑ i, ‖A i j‖ ^ (2 : ℕ) := fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hB : ∀ j, 0 ≤ ∑ i, ‖B i j‖ ^ (2 : ℕ) := fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hAsq : ∑ j, columnL2Norm A j ^ (2 : ℕ) =
      ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ) := by
    calc
      (∑ j, columnL2Norm A j ^ (2 : ℕ)) =
          ∑ j, ∑ i, ‖A i j‖ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Real.sq_sqrt (hA j)
      _ = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ) := Finset.sum_comm
  have hBsq : ∑ j, columnL2Norm B j ^ (2 : ℕ) =
      ∑ i, ∑ j, ‖B i j‖ ^ (2 : ℕ) := by
    calc
      (∑ j, columnL2Norm B j ^ (2 : ℕ)) =
          ∑ j, ∑ i, ‖B i j‖ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Real.sq_sqrt (hB j)
      _ = ∑ i, ∑ j, ‖B i j‖ ^ (2 : ℕ) := Finset.sum_comm
  rw [hAsq, hBsq] at h
  exact h

private theorem sum_rowL2Norm_mul_columnL2Norm_le
    {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    ∑ i, rowL2Norm A i * columnL2Norm B i ≤
      entryL2Norm A * entryL2Norm B := by
  rw [← entryL2Norm_transpose A]
  simpa only [rowL2Norm, columnL2Norm, Matrix.transpose_apply] using
    sum_columnL2Norm_mul_columnL2Norm_le Aᵀ B

private theorem trace_comp_twoSided_factorization
    {D : ℕ} (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (P A E : Matrix (Fin D) (Fin D) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (F.comp ((LinearMap.mulLeft ℂ (P * Aᴴ)).comp
          (LinearMap.mulRight ℂ (P * E)))) =
      ∑ a, ∑ d, Matrix.trace
        ((twoSidedTraceRightFactor P A a d)ᴴ *
          F (twoSidedTraceLeftFactor P E a d)) := by
  classical
  rw [linearMap_trace_eq_sum_apply_single]
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp_rw [twoSided_apply_single_factorization, map_sum, map_smul,
    Matrix.sum_apply, Matrix.smul_apply]
  simp only [smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, twoSidedTraceRightFactor, star_mul, star_star]
  rw [Finset.sum_comm_cycle]
  congr with a
  rw [Finset.sum_comm_cycle]
  congr with d
  rw [Finset.sum_comm]
  congr with b
  congr with c
  ring

private theorem weightedLinearEquiv_conj_twoSidedMul
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    let s := CFC.sqrt ρ
    let P := s⁻¹
    let A := B * s
    let E := C * s
    (weightedLinearEquiv ρ hρ).conj
        ((LinearMap.mulLeft ℂ Bᴴ).comp (LinearMap.mulRight ℂ C)) =
      (LinearMap.mulLeft ℂ (P * Aᴴ)).comp (LinearMap.mulRight ℂ (P * E)) := by
  dsimp only
  apply LinearMap.ext
  intro X
  change (Bᴴ * (X * (CFC.sqrt ρ)⁻¹ * C)) * CFC.sqrt ρ =
    ((CFC.sqrt ρ)⁻¹ * (B * CFC.sqrt ρ)ᴴ) *
      (X * ((CFC.sqrt ρ)⁻¹ * (C * CFC.sqrt ρ)))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_cfc_sqrt,
    ← Matrix.mul_assoc (CFC.sqrt ρ)⁻¹ (CFC.sqrt ρ) Bᴴ,
    Matrix.nonsing_inv_mul _ hρ.isUnit_det_cfc_sqrt, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

private theorem norm_trace_comp_twoSided_le
    {D : ℕ} (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (P A E : Matrix (Fin D) (Fin D) ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hF : ∀ X, entryL2Norm (F X) ≤ K * entryL2Norm X) :
    ‖LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (F.comp ((LinearMap.mulLeft ℂ (P * Aᴴ)).comp
          (LinearMap.mulRight ℂ (P * E))))‖ ≤
      K * (entryL2Norm P * entryL2Norm A) *
        (entryL2Norm E * entryL2Norm P) := by
  rw [trace_comp_twoSided_factorization]
  calc
    ‖∑ a, ∑ d, Matrix.trace
        ((twoSidedTraceRightFactor P A a d)ᴴ *
          F (twoSidedTraceLeftFactor P E a d))‖ ≤
        ∑ a, ∑ d, ‖Matrix.trace
          ((twoSidedTraceRightFactor P A a d)ᴴ *
            F (twoSidedTraceLeftFactor P E a d))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ a, ∑ d, K *
        (columnL2Norm P a * columnL2Norm A a) *
          (rowL2Norm E d * columnL2Norm P d) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro d _
      calc
        ‖Matrix.trace ((twoSidedTraceRightFactor P A a d)ᴴ *
            F (twoSidedTraceLeftFactor P E a d))‖ ≤
            entryL2Norm (twoSidedTraceRightFactor P A a d) *
              entryL2Norm (F (twoSidedTraceLeftFactor P E a d)) :=
          norm_trace_conjTranspose_mul_le_entryL2Norm _ _
        _ ≤ entryL2Norm (twoSidedTraceRightFactor P A a d) *
            (K * entryL2Norm (twoSidedTraceLeftFactor P E a d)) :=
          mul_le_mul_of_nonneg_left (hF _) (Real.sqrt_nonneg _)
        _ = K * (columnL2Norm P a * columnL2Norm A a) *
            (rowL2Norm E d * columnL2Norm P d) := by
          rw [entryL2Norm_twoSidedTraceRightFactor,
            entryL2Norm_twoSidedTraceLeftFactor]
          ring
    _ = K * (∑ a, columnL2Norm P a * columnL2Norm A a) *
        ∑ d, rowL2Norm E d * columnL2Norm P d := by
      symm
      calc
        K * (∑ a, columnL2Norm P a * columnL2Norm A a) *
            (∑ d, rowL2Norm E d * columnL2Norm P d) =
            (∑ a, columnL2Norm P a * columnL2Norm A a) *
              (K * ∑ d, rowL2Norm E d * columnL2Norm P d) := by ring
        _ = ∑ a, (columnL2Norm P a * columnL2Norm A a) *
              (K * ∑ d, rowL2Norm E d * columnL2Norm P d) :=
          Finset.sum_mul _ _ _
        _ = ∑ a, ∑ d, K *
            (columnL2Norm P a * columnL2Norm A a) *
              (rowL2Norm E d * columnL2Norm P d) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
    _ ≤ K * (entryL2Norm P * entryL2Norm A) *
        (entryL2Norm E * entryL2Norm P) := by
      have hleft := sum_columnL2Norm_mul_columnL2Norm_le P A
      have hright := sum_rowL2Norm_mul_columnL2Norm_le E P
      have hright_nonneg : 0 ≤ ∑ d, rowL2Norm E d * columnL2Norm P d :=
        Finset.sum_nonneg fun _ _ ↦
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc
        K * (∑ a, columnL2Norm P a * columnL2Norm A a) *
            (∑ d, rowL2Norm E d * columnL2Norm P d) ≤
            K * (entryL2Norm P * entryL2Norm A) *
              (∑ d, rowL2Norm E d * columnL2Norm P d) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hleft hK) hright_nonneg
        _ ≤ K * (entryL2Norm P * entryL2Norm A) *
            (entryL2Norm E * entryL2Norm P) :=
          mul_le_mul_of_nonneg_left hright
            (mul_nonneg hK (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

end

/-- The algebraic trace pairing of a linear map with the two-sided multiplier
`X ↦ Bᴴ * X * C` is bounded by its operator norm for the `ρ`-weighted
Hilbert--Schmidt structure.  The weight loss is exactly
`(Matrix.trace ρ⁻¹).re`; in particular, no dimension-dependent factor occurs. -/
theorem norm_trace_comp_twoSidedMul_le_weighted
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (F.comp ((LinearMap.mulLeft ℂ Bᴴ).comp (LinearMap.mulRight ℂ C)))‖ ≤
      (Matrix.trace ρ⁻¹).re *
        ‖(Module.End.toContinuousLinearMap (𝕜 := ℂ)
          (Matrix (Fin D) (Fin D) ℂ)) F‖ * ‖B‖ * ‖C‖ := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ)
    (Matrix (Fin D) (Fin D) ℂ)
  let s := CFC.sqrt ρ
  let P := s⁻¹
  let A := B * s
  let E := C * s
  let e := weightedLinearEquiv ρ hρ
  let G := e.conj F
  let K := ‖Φ F‖
  have hK : 0 ≤ K := norm_nonneg _
  have hG : ∀ X, entryL2Norm (G X) ≤ K * entryL2Norm X := by
    intro X
    have hop := (Φ F).le_opNorm (e.symm X)
    have hinv : (e.symm X) * s = X := by
      change (X * s⁻¹) * s = X
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ.isUnit_det_cfc_sqrt,
        Matrix.mul_one]
    calc
      entryL2Norm (G X) = ‖F (e.symm X)‖ := by
        change entryL2Norm (F (e.symm X) * s) = ‖F (e.symm X)‖
        exact entryL2Norm_mul_sqrt_eq_weighted_norm ρ hρ _
      _ ≤ K * ‖e.symm X‖ := hop
      _ = K * entryL2Norm X := by
        rw [← entryL2Norm_mul_sqrt_eq_weighted_norm ρ hρ (e.symm X), hinv]
  have htrace :
      LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
          (F.comp ((LinearMap.mulLeft ℂ Bᴴ).comp (LinearMap.mulRight ℂ C))) =
        LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
          (G.comp ((LinearMap.mulLeft ℂ (P * Aᴴ)).comp
            (LinearMap.mulRight ℂ (P * E)))) := by
    rw [← weightedLinearEquiv_conj_twoSidedMul ρ hρ B C]
    have hcomp :
        G.comp (e.conj ((LinearMap.mulLeft ℂ Bᴴ).comp
          (LinearMap.mulRight ℂ C))) =
          e.conj (F.comp ((LinearMap.mulLeft ℂ Bᴴ).comp
            (LinearMap.mulRight ℂ C))) := by
      apply LinearMap.ext
      intro X
      change e (F (e.symm (e (((LinearMap.mulLeft ℂ Bᴴ).comp
        (LinearMap.mulRight ℂ C)) (e.symm X))))) =
          e (F (((LinearMap.mulLeft ℂ Bᴴ).comp
            (LinearMap.mulRight ℂ C)) (e.symm X)))
      rw [e.symm_apply_apply]
    rw [hcomp, LinearMap.trace_conj']
  rw [htrace]
  have hbound := norm_trace_comp_twoSided_le G P A E K hK hG
  calc
    ‖LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
        (G.comp ((LinearMap.mulLeft ℂ (P * Aᴴ)).comp
          (LinearMap.mulRight ℂ (P * E))))‖ ≤
        K * (entryL2Norm P * entryL2Norm A) *
          (entryL2Norm E * entryL2Norm P) := hbound
    _ = (Matrix.trace ρ⁻¹).re * K * ‖B‖ * ‖C‖ := by
      have hA : entryL2Norm A = ‖B‖ := by
        exact entryL2Norm_mul_sqrt_eq_weighted_norm ρ hρ B
      have hE : entryL2Norm E = ‖C‖ := by
        exact entryL2Norm_mul_sqrt_eq_weighted_norm ρ hρ C
      have hP : entryL2Norm P ^ (2 : ℕ) = (Matrix.trace ρ⁻¹).re :=
        entryL2Norm_inv_sqrt_sq ρ hρ
      rw [hA, hE]
      calc
        K * (entryL2Norm P * ‖B‖) * (‖C‖ * entryL2Norm P) =
            K * ‖B‖ * ‖C‖ * entryL2Norm P ^ (2 : ℕ) := by ring
        _ = K * ‖B‖ * ‖C‖ * (Matrix.trace ρ⁻¹).re := by rw [hP]
        _ = (Matrix.trace ρ⁻¹).re * K * ‖B‖ * ‖C‖ := by ring

end Matrix
