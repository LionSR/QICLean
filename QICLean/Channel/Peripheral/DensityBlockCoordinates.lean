/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TraceReindex
import QICLean.Channel.FixedPoint.ExtremeDensityStates
import QICLean.Channel.FixedPoint.WolfTheorem614

/-!
# Density-block coordinates on the peripheral image

This file packages the coordinate maps used in the proof of Wolf's Theorem 6.16.
The fixed-point description from `IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`
has one zero summand and nonzero summands of the form `sigma k ⊗ X k`.  The embedding below
uses exactly those witnesses.  Its left inverse removes the zero summand, compresses to each
diagonal block, and takes the partial trace over the density factor.

The formal factor order is the one established by the fixed-point theorem: `sigma k ⊗ X k`,
whereas Wolf writes the full-matrix factor first.  No second block decomposition is introduced.

## Main declarations

* `Matrix.densityBlockWithZeroEmbedding`
* `Matrix.densityBlockWithZeroCompression`
* `Matrix.densityBlockWithZeroCompression_embedding`

## Reference

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.16;
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1641--1659.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators Kronecker

noncomputable section

namespace Matrix

private noncomputable def densityBlockTensorEmbedding
    {K : ℕ} {d m : Fin K → ℕ}
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ) :
    (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ) where
  toFun X k := sigma k ⊗ₖ X k
  map_add' X Y := by
    funext k
    exact Matrix.kronecker_add (sigma k) (X k) (Y k)
  map_smul' c X := by
    funext k
    exact Matrix.kronecker_smul c (sigma k) (X k)

private noncomputable def zeroBottomRightEmbedding
    {D n : ℕ} :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin (D - n) ⊕ Fin n) (Fin (D - n) ⊕ Fin n) ℂ where
  toFun A := Matrix.fromBlocks 0 0 0 A
  map_add' A B := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp
  map_smul' c A := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp

private theorem trace_zeroBottomRightEmbedding
    {D n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Matrix.fromBlocks
      (0 : Matrix (Fin (D - n)) (Fin (D - n)) ℂ) 0 0 A) = Matrix.trace A := by
  rw [Matrix.trace]
  rw [Fintype.sum_sum_type]
  simp [Matrix.trace, Matrix.diag]

private noncomputable def bottomRightCompression
    {D n : ℕ} :
    Matrix (Fin (D - n) ⊕ Fin n) (Fin (D - n) ⊕ Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin n) (Fin n) ℂ where
  toFun A := A.toBlocks₂₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def densityBlockFamilyCompression
    {K : ℕ} {d m : Fin K → ℕ} :
    Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →ₗ[ℂ]
      (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) where
  toFun A k := Matrix.partialTraceLeft
    (Matrix.directSumBlockCompression (m := m) (d := d) k A)
  map_add' A B := by
    funext k i j
    simp only [Matrix.partialTraceLeft_apply, map_add, Matrix.add_apply, Pi.add_apply,
      Finset.sum_add_distrib]
  map_smul' c A := by
    funext k i j
    simp only [Matrix.partialTraceLeft_apply, map_smul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]

/-- Embed a family of full-matrix factors into the zero-extended density-block space
provided by Wolf Theorem 6.14.

The value at `X` is
`U * reindex e₀ e₀ (fromBlocks 0 0 0 (reindex e e (blockDiagonal' (sigma ⊗ X)))) * U†`.
The use of `sigma k ⊗ X k` follows QICLean's established factor order. -/
noncomputable def densityBlockWithZeroEmbedding
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ) :
    (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ :=
  (Matrix.unitaryReindexLinearEquiv e₀ U hU).symm.toLinearMap.comp
    (zeroBottomRightEmbedding.comp
      ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
        (Matrix.directSumDiagonalEmbedding.comp
          (densityBlockTensorEmbedding sigma))))

@[simp]
theorem densityBlockWithZeroEmbedding_apply
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    densityBlockWithZeroEmbedding e e₀ U hU sigma X =
      U * Matrix.reindex e₀ e₀
        (Matrix.fromBlocks 0 0 0
          (Matrix.reindex e e
            (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))) * star U := by
  simp [densityBlockWithZeroEmbedding, zeroBottomRightEmbedding,
    densityBlockTensorEmbedding, Matrix.unitaryReindexLinearEquiv_symm_apply]

/-- Recover the full-matrix factors from Wolf's zero-extended density-block coordinates.

After changing to the unitary coordinates, this retains the bottom-right nonzero summand,
undoes its reindexing, compresses to each diagonal block, and traces over `Fin (m k)`. -/
noncomputable def densityBlockWithZeroCompression
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :=
  densityBlockFamilyCompression.comp
    ((Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
      (bottomRightCompression.comp
        (Matrix.unitaryReindexLinearEquiv e₀ U hU).toLinearMap))

@[simp]
theorem densityBlockWithZeroCompression_apply
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (B : Matrix (Fin D) (Fin D) ℂ) (k : Fin K) :
    densityBlockWithZeroCompression e e₀ U hU B k =
      Matrix.partialTraceLeft
        (Matrix.directSumBlockCompression (m := m) (d := d) k
          (Matrix.reindex e.symm e.symm
            (Matrix.unitaryReindexLinearEquiv e₀ U hU B).toBlocks₂₂)) := by
  rfl

/-- Taking density-block coordinates after embedding recovers the original family when
the fixed density factors have trace one. -/
@[simp]
theorem densityBlockWithZeroCompression_embedding
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    densityBlockWithZeroCompression e e₀ U hU
        (densityBlockWithZeroEmbedding e e₀ U hU sigma X) = X := by
  let Phi := Matrix.unitaryReindexLinearEquiv e₀ U hU
  let A : Matrix (Fin (D - n) ⊕ Fin n) (Fin (D - n) ⊕ Fin n) ℂ :=
    Matrix.fromBlocks 0 0 0
      (Matrix.reindex e e
        (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))
  have hcoord : Phi (densityBlockWithZeroEmbedding e e₀ U hU sigma X) = A := by
    change Phi (Phi.symm A) = A
    exact Phi.apply_symm_apply A
  funext k
  rw [densityBlockWithZeroCompression_apply, hcoord]
  simp [A, Matrix.partialTraceLeft_kronecker, hsigmaTrace]

/-- Density-block compression preserves positive semidefiniteness componentwise. -/
theorem densityBlockWithZeroCompression_posSemidef
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    {B : Matrix (Fin D) (Fin D) ℂ} (hB : B.PosSemidef) :
    ∀ k, (densityBlockWithZeroCompression e e₀ U hU B k).PosSemidef := by
  intro k
  rw [densityBlockWithZeroCompression_apply]
  apply Matrix.PosSemidef.partialTraceLeft
  apply Matrix.directSumBlockCompression_isPositiveMap k
  have hcoord : (Matrix.unitaryReindexLinearEquiv e₀ U hU B).PosSemidef :=
    Matrix.unitaryReindexLinearEquiv_posSemidef e₀ U hU hB
  have hbottom : (Matrix.unitaryReindexLinearEquiv e₀ U hU B).toBlocks₂₂.PosSemidef := by
    exact hcoord.submatrix Sum.inr
  simpa only [Matrix.reindex_apply, Equiv.symm_symm,
    Matrix.posSemidef_submatrix_equiv] using hbottom

/-- Embedding componentwise positive-semidefinite full-matrix factors gives a positive
semidefinite ambient matrix. -/
theorem densityBlockWithZeroEmbedding_posSemidef
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigma : ∀ k, (sigma k).PosSemidef)
    {X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ}
    (hX : ∀ k, (X k).PosSemidef) :
    (densityBlockWithZeroEmbedding e e₀ U hU sigma X).PosSemidef := by
  let Phi := Matrix.unitaryReindexLinearEquiv e₀ U hU
  let A : Matrix (Fin (D - n) ⊕ Fin n) (Fin (D - n) ⊕ Fin n) ℂ :=
    Matrix.fromBlocks 0 0 0
      (Matrix.reindex e e
        (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))
  change (Phi.symm A).PosSemidef
  apply Matrix.unitaryReindexLinearEquiv_symm_posSemidef e₀ U hU
  apply Matrix.PosSemidef.fromBlocks_diag Matrix.PosSemidef.zero
  have hblocks :
      (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k).PosSemidef :=
    (Matrix.blockDiagonal'_posSemidef_iff
      (fun k ↦ sigma k ⊗ₖ X k)).2 fun k ↦ (hsigma k).kronecker (hX k)
  simpa only [Matrix.reindex_apply, Matrix.posSemidef_submatrix_equiv] using hblocks

/-- Positive semidefiniteness in density-block coordinates is exactly componentwise
positive semidefiniteness of the full-matrix factors. -/
theorem densityBlockWithZeroEmbedding_posSemidef_iff
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigma : ∀ k, (sigma k).PosSemidef)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    (densityBlockWithZeroEmbedding e e₀ U hU sigma X).PosSemidef ↔
      ∀ k, (X k).PosSemidef := by
  constructor
  · intro hX
    have hcompressed := densityBlockWithZeroCompression_posSemidef
      e e₀ U hU hX
    simpa only [densityBlockWithZeroCompression_embedding
      e e₀ U hU sigma hsigmaTrace X] using hcompressed
  · exact densityBlockWithZeroEmbedding_posSemidef e e₀ U hU sigma hsigma

/-- The ambient trace of an embedded density-block family is the sum of the traces of
its full-matrix factors. -/
theorem trace_densityBlockWithZeroEmbedding
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    (densityBlockWithZeroEmbedding e e₀ U hU sigma X).trace =
      ∑ k, (X k).trace := by
  rw [densityBlockWithZeroEmbedding_apply]
  have hUleft : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  let A : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.reindex e e
      (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)
  change Matrix.trace
    (U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U) =
      ∑ k, (X k).trace
  calc
    Matrix.trace
        (U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U) =
        Matrix.trace
          (star U * (U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A))) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        ((star U * U) * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A)) := by
      rw [← Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A)) := by
      rw [hUleft, Matrix.one_mul]
    _ = Matrix.trace (Matrix.fromBlocks 0 0 0 A) := Matrix.trace_reindex e₀ _
    _ = Matrix.trace A := trace_zeroBottomRightEmbedding A
    _ = Matrix.trace
        (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k) := Matrix.trace_reindex e _
    _ = ∑ k, Matrix.trace (sigma k ⊗ₖ X k) := Matrix.trace_blockDiagonal' _
    _ = ∑ k, (X k).trace := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.trace_kronecker, hsigmaTrace, one_mul]

/-- The trace-one positive cone in density-block coordinates is exactly the direct-sum
density-state space used for Wolf's relative extreme points. -/
theorem densityBlockWithZeroEmbedding_mem_densityMatrices_iff
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigma : ∀ k, (sigma k).PosSemidef)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    densityBlockWithZeroEmbedding e e₀ U hU sigma X ∈ densityMatrices D ↔
      X ∈ directSumDensityMatrices d := by
  simp only [mem_densityMatrices, Matrix.mem_directSumDensityMatrices,
    densityBlockWithZeroEmbedding_posSemidef_iff e e₀ U hU sigma hsigma hsigmaTrace X,
    trace_densityBlockWithZeroEmbedding e e₀ U hU sigma hsigmaTrace X]

/-- Every encoded density-block family is fixed under the coordinate equation supplied by
`IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`. -/
theorem densityBlockWithZeroEmbedding_fixed
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    {P : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hfixed : ∀ B, P B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    P (densityBlockWithZeroEmbedding e e₀ U hU sigma X) =
      densityBlockWithZeroEmbedding e e₀ U hU sigma X := by
  apply (hfixed _).mpr
  refine ⟨X, ?_⟩
  rw [densityBlockWithZeroEmbedding_apply]
  have hUleft : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    star U *
          (U * Matrix.reindex e₀ e₀
            (Matrix.fromBlocks 0 0 0
              (Matrix.reindex e e
                (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))) * star U) * U =
        (star U * U) * Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))) * (star U * U) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.reindex e₀ e₀
        (Matrix.fromBlocks 0 0 0
          (Matrix.reindex e e
            (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))) := by
      rw [hUleft]
      simp

/-- Encoding the compressed coordinates of a fixed point reconstructs that fixed point.

The hypothesis is exactly the fixed-point equation returned by
`IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`; in particular, this theorem
does not introduce a second decomposition or strengthen the fixed-point contract. -/
theorem densityBlockWithZeroEmbedding_compression_of_fixed
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {P : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hfixed : ∀ B, P B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    {B : Matrix (Fin D) (Fin D) ℂ} (hB : P B = B) :
    densityBlockWithZeroEmbedding e e₀ U hU sigma
        (densityBlockWithZeroCompression e e₀ U hU B) = B := by
  obtain ⟨X, hBcoord⟩ := (hfixed B).mp hB
  let A : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.reindex e e
      (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)
  have hcoord : Matrix.unitaryReindexLinearEquiv e₀ U hU B =
      Matrix.fromBlocks 0 0 0 A := by
    rw [Matrix.unitaryReindexLinearEquiv_apply, hBcoord]
    simp [A]
  have hcompression : densityBlockWithZeroCompression e e₀ U hU B = X := by
    funext k
    rw [densityBlockWithZeroCompression_apply, hcoord]
    simp [A, Matrix.partialTraceLeft_kronecker, hsigmaTrace]
  rw [hcompression, densityBlockWithZeroEmbedding_apply]
  rw [← hBcoord]
  have hUright : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  calc
    U * (star U * B * U) * star U =
        (U * star U) * B * (U * star U) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [hUright]; simp

end Matrix
