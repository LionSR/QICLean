/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Channel.DirectSumConditionalExpectation
import QICLean.Channel.FixedPoint.AbstractCornerFixedPoints
import QICLean.Channel.FixedPoint.AbstractMaximalRank
import QICLean.Channel.FixedPoint.WeightedCornerFixedPoints
import QICLean.Channel.FixedPoint.WolfTheorem614

/-!
# Weighted fixed points of positive maps

This file formalizes the source-general form of Wolf Corollary 6.7.  Its
multiplication argument follows the density-block description of Wolf
Theorem 6.14: after weighting by a positive-definite stationary matrix, the
blocks `sigma k tensor X k` become the coordinate right-factor algebra
`1 tensor X k`.

## Main declarations

* `IsPositiveMap.weightedCornerFixedPointsStarSubalgebra` constructs the
  support-correct weighted fixed-point star-algebra under Wolf's positive,
  trace-preserving, and trace-adjoint Schwarz hypotheses.
* `IsPositiveMap.mem_weightedCornerFixedPointsStarSubalgebra_iff_inverseSandwich`
  identifies its carrier with the support-inverse-square-root conjugate of
  the full fixed-point space at every maximum-rank stationary density.
* `IsPositiveMap.wolfCorollary67` states Wolf Corollary 6.7 with its printed
  hypotheses and its quantification over every maximum-rank stationary
  density matrix.

## Reference

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.7;
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 1497--1510.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace IsPositiveMap

variable {D : Nat}

local notation "Mat" => Matrix (Fin D) (Fin D) Complex

/-- Multiplication closure in the full-support step of Wolf Corollary 6.7.

The proof uses the density blocks from Wolf Theorem 6.14.  If the fixed
matrices have blocks `sigma k tensor A k` and `sigma k tensor B k`, while the
positive-definite stationary matrix has blocks `sigma k tensor R k`, then
their weighted product has blocks
`sigma k tensor (A k * (R k)^{-1} * B k)` and is therefore fixed. -/
theorem weightedFixed_mul_of_posDef
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosDef) (hrhoFix : T rho = rho)
    {Y1 Y2 : Mat}
    (hY1 : T (CFC.sqrt rho * Y1 * CFC.sqrt rho) =
      CFC.sqrt rho * Y1 * CFC.sqrt rho)
    (hY2 : T (CFC.sqrt rho * Y2 * CFC.sqrt rho) =
      CFC.sqrt rho * Y2 * CFC.sqrt rho) :
    T (CFC.sqrt rho * (Y1 * Y2) * CFC.sqrt rho) =
      CFC.sqrt rho * (Y1 * Y2) * CFC.sqrt rho := by
  classical
  let S : Mat := CFC.sqrt rho
  let A1 : Mat := S * Y1 * S
  let A2 : Mat := S * Y2 * S
  obtain ⟨K, d, m, e, U, sigma, hU, hd, hm, hsigmaPsd, hsigmaTrace, _, hfixed⟩ :=
    hT.exists_block_densities_of_meanErgodicProjection
      hTP hSchwarz hrho hrhoFix
  obtain ⟨R, hRcoord⟩ := (hfixed rho).mp hrhoFix
  obtain ⟨X1, hX1coord⟩ := (hfixed A1).mp (by simpa [A1, S] using hY1)
  obtain ⟨X2, hX2coord⟩ := (hfixed A2).mp (by simpa [A2, S] using hY2)
  let Phi := Matrix.unitaryReindexLinearEquiv e U hU
  have hPhiR : Phi rho =
      Matrix.blockDiagonal' (fun k ↦ sigma k ⊗ₖ R k) := by
    rw [Matrix.unitaryReindexLinearEquiv_apply, hRcoord]
    ext i j
    simp
  have hPhiX1 : Phi A1 =
      Matrix.blockDiagonal' (fun k ↦ sigma k ⊗ₖ X1 k) := by
    rw [Matrix.unitaryReindexLinearEquiv_apply, hX1coord]
    ext i j
    simp
  have hPhiX2 : Phi A2 =
      Matrix.blockDiagonal' (fun k ↦ sigma k ⊗ₖ X2 k) := by
    rw [Matrix.unitaryReindexLinearEquiv_apply, hX2coord]
    ext i j
    simp
  let Uunitary : unitary (Matrix (Fin D) (Fin D) Complex) := ⟨U, hU⟩
  have hUunit : IsUnit U := ⟨Unitary.toUnits Uunitary, rfl⟩
  have hconjRho : (star U * rho * U).PosDef := by
    simpa only [star_eq_conjTranspose] using
      hrho.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_iff_isUnit.mpr hUunit)
  have hPhiRPosDef : (Phi rho).PosDef := by
    rw [Matrix.unitaryReindexLinearEquiv_apply]
    exact hconjRho.submatrix e.injective
  have hblocksPosDef :
      (Matrix.blockDiagonal' (fun k ↦ sigma k ⊗ₖ R k)).PosDef := by
    rwa [hPhiR] at hPhiRPosDef
  have hblockPosDef : ∀ k, (sigma k ⊗ₖ R k).PosDef := by
    intro k
    have hprincipal := hblocksPosDef.submatrix
      (e := fun i ↦ ⟨k, i⟩)
      (fun _ _ hij ↦ eq_of_heq (Sigma.mk.inj_iff.mp hij).2)
    have heq :
        (Matrix.blockDiagonal' (fun j ↦ sigma j ⊗ₖ R j)).submatrix
            (fun i ↦ ⟨k, i⟩) (fun i ↦ ⟨k, i⟩) =
          sigma k ⊗ₖ R k := by
      ext i j
      exact Matrix.blockDiagonal'_apply_eq
        (fun q ↦ sigma q ⊗ₖ R q) k i j
    rwa [heq] at hprincipal
  have hRPosDef : ∀ k, (R k).PosDef := by
    intro k
    let _ : Nonempty (Fin (m k)) := Fin.pos_iff_nonempty.mp (hm k)
    have hpartial := (hblockPosDef k).partialTraceLeft
    simpa only [Matrix.partialTraceLeft_kronecker, hsigmaTrace k, one_smul]
      using hpartial
  have hsigmaPosDef : ∀ k, (sigma k).PosDef := by
    intro k
    let _ : Nonempty (Fin (m k)) := Fin.pos_iff_nonempty.mp (hm k)
    let _ : Nonempty (Fin (d k)) := Fin.pos_iff_nonempty.mp (hd k)
    exact (hblockPosDef k).left_of_kronecker_of_trace_eq_one (hsigmaTrace k)
  let blockR := Matrix.blockDiagonal' (fun k ↦ sigma k ⊗ₖ R k)
  let blockRInv := Matrix.blockDiagonal'
    (fun k ↦ (sigma k)⁻¹ ⊗ₖ (R k)⁻¹)
  have hblockMulInv : blockR * blockRInv = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    have hfamily :
        (fun k ↦ (sigma k ⊗ₖ R k) * ((sigma k)⁻¹ ⊗ₖ (R k)⁻¹)) =
          (1 : ∀ k, Matrix (Fin (m k) × Fin (d k))
            (Fin (m k) × Fin (d k)) Complex) := by
      funext k
      rw [← Matrix.mul_kronecker_mul,
        Matrix.mul_nonsing_inv _
          ((Matrix.isUnit_iff_isUnit_det _).mp (hsigmaPosDef k).isUnit),
        Matrix.mul_nonsing_inv _
          ((Matrix.isUnit_iff_isUnit_det _).mp (hRPosDef k).isUnit),
        Matrix.one_kronecker_one]
      rfl
    rw [hfamily]
    exact Matrix.blockDiagonal'_one
  have hblockInv : blockR⁻¹ = blockRInv :=
    Matrix.inv_eq_right_inv hblockMulInv
  have hrhoDet : IsUnit rho.det :=
    (Matrix.isUnit_iff_isUnit_det rho).mp hrho.isUnit
  have hPhiInv : Phi rho⁻¹ = (Phi rho)⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.unitaryReindexLinearEquiv_mul,
      Matrix.mul_nonsing_inv rho hrhoDet,
      Matrix.unitaryReindexLinearEquiv_one]
  let C : Mat := A1 * rho⁻¹ * A2
  have hPhiC : Phi C = Matrix.blockDiagonal'
      (fun k ↦ sigma k ⊗ₖ (X1 k * (R k)⁻¹ * X2 k)) := by
    dsimp only [C]
    rw [Matrix.unitaryReindexLinearEquiv_mul,
      Matrix.unitaryReindexLinearEquiv_mul,
      hPhiX1, hPhiInv, hPhiR, hblockInv, hPhiX2]
    dsimp only [blockRInv]
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext k
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp (hsigmaPosDef k).isUnit),
      Matrix.one_mul]
  have hCfix : T C = C := by
    apply (hfixed C).mpr
    refine ⟨fun k ↦ X1 k * (R k)⁻¹ * X2 k, ?_⟩
    calc
      star U * C * U = Matrix.reindex e e (Phi C) := by
        rw [Matrix.unitaryReindexLinearEquiv_apply]
        ext i j
        simp
      _ = Matrix.reindex e e (Matrix.blockDiagonal'
          (fun k ↦ sigma k ⊗ₖ (X1 k * (R k)⁻¹ * X2 k))) := by
        rw [hPhiC]
  have hSdet : IsUnit S.det := by
    simpa only [S] using hrho.isUnit_det_cfc_sqrt
  have hSS : S * S = rho := by
    simpa only [S] using CFC.sqrt_mul_sqrt_self rho hrho.posSemidef.nonneg
  have hSmulInv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hSinvMul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hrhoInv : rho⁻¹ = S⁻¹ * S⁻¹ := by
    apply Matrix.inv_eq_right_inv
    calc
      rho * (S⁻¹ * S⁻¹) = (S * S) * (S⁻¹ * S⁻¹) := by rw [hSS]
      _ = S * (S * S⁻¹) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S * 1 * S⁻¹ := congrArg (fun Z ↦ S * Z * S⁻¹) hSmulInv
      _ = S * S⁻¹ := by rw [Matrix.mul_one]
      _ = 1 := hSmulInv
  have hCeq : C = S * (Y1 * Y2) * S := by
    dsimp only [C, A1, A2]
    calc
      (S * Y1 * S) * rho⁻¹ * (S * Y2 * S) =
          (S * Y1 * S) * (S⁻¹ * S⁻¹) * (S * Y2 * S) := by rw [hrhoInv]
      _ = S * Y1 * (S * S⁻¹) * (S⁻¹ * S) * Y2 * S := by
        simp only [Matrix.mul_assoc]
      _ = S * Y1 * 1 * 1 * Y2 * S := by rw [hSmulInv, hSinvMul]
      _ = S * (Y1 * Y2) * S := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  simpa only [S, ← hCeq] using hCfix

/-- The source-general full-support weighted fixed points form a star
subalgebra.  Multiplication is the density-block calculation in
`weightedFixed_mul_of_posDef`; the other operations use only linearity and
positivity of `T`. -/
noncomputable def weightedFixedPointsStarSubalgebra
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosDef) (hrhoFix : T rho = rho) :
    StarSubalgebra Complex Mat where
  carrier := {Y | T (CFC.sqrt rho * Y * CFC.sqrt rho) =
    CFC.sqrt rho * Y * CFC.sqrt rho}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change T (CFC.sqrt rho * X * CFC.sqrt rho) =
      CFC.sqrt rho * X * CFC.sqrt rho at hX
    change T (CFC.sqrt rho * Y * CFC.sqrt rho) =
      CFC.sqrt rho * Y * CFC.sqrt rho at hY
    change T (CFC.sqrt rho * (X + Y) * CFC.sqrt rho) =
      CFC.sqrt rho * (X + Y) * CFC.sqrt rho
    rw [Matrix.mul_add, Matrix.add_mul, T.map_add, hX, hY]
  one_mem' := by
    change T (CFC.sqrt rho * (1 : Mat) * CFC.sqrt rho) =
      CFC.sqrt rho * (1 : Mat) * CFC.sqrt rho
    rw [Matrix.mul_one, CFC.sqrt_mul_sqrt_self rho hrho.posSemidef.nonneg]
    exact hrhoFix
  mul_mem' := weightedFixed_mul_of_posDef hT hTP hSchwarz hrho hrhoFix
  algebraMap_mem' := by
    intro c
    change T (CFC.sqrt rho * algebraMap Complex Mat c * CFC.sqrt rho) =
      CFC.sqrt rho * algebraMap Complex Mat c * CFC.sqrt rho
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, CFC.sqrt_mul_sqrt_self rho hrho.posSemidef.nonneg,
      T.map_smul, hrhoFix]
  star_mem' := by
    intro Y hY
    change T (CFC.sqrt rho * Y * CFC.sqrt rho) =
      CFC.sqrt rho * Y * CFC.sqrt rho at hY
    change T (CFC.sqrt rho * star Y * CFC.sqrt rho) =
      CFC.sqrt rho * star Y * CFC.sqrt rho
    have hSstar : (CFC.sqrt rho)ᴴ = CFC.sqrt rho :=
      Matrix.conjTranspose_cfc_sqrt rho
    have hconj : CFC.sqrt rho * star Y * CFC.sqrt rho =
        (CFC.sqrt rho * Y * CFC.sqrt rho)ᴴ := by
      simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul,
        hSstar, Matrix.mul_assoc]
    rw [hconj, hT.map_conjTranspose, hY]

/-- Membership in the source-general full-support weighted fixed-point
star-subalgebra is Wolf's displayed fixed-point condition. -/
@[simp] theorem mem_weightedFixedPointsStarSubalgebra
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosDef) (hrhoFix : T rho = rho) (Y : Mat) :
    Y ∈ weightedFixedPointsStarSubalgebra hT hTP hSchwarz hrho hrhoFix ↔
      T (CFC.sqrt rho * Y * CFC.sqrt rho) =
        CFC.sqrt rho * Y * CFC.sqrt rho :=
  Iff.rfl

/-- Multiplication closure after taking the inverse square root on the support
of a possibly singular stationary matrix.  The map is compressed to that
support, `weightedFixed_mul_of_posDef` applies there by the density-block route
of Theorem 6.14, and the result is extended back by zero. -/
private theorem weightedCornerFixed_mul
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosSemidef) (hrhoFix : T rho = rho)
    {Y1 Y2 : Mat}
    (hY1mem : Kraus.stationaryProj hrho * Y1 * Kraus.stationaryProj hrho = Y1)
    (hY2mem : Kraus.stationaryProj hrho * Y2 * Kraus.stationaryProj hrho = Y2)
    (hY1 : T (CFC.sqrt rho * Y1 * CFC.sqrt rho) =
      CFC.sqrt rho * Y1 * CFC.sqrt rho)
    (hY2 : T (CFC.sqrt rho * Y2 * CFC.sqrt rho) =
      CFC.sqrt rho * Y2 * CFC.sqrt rho) :
    T (CFC.sqrt rho * (Y1 * Y2) * CFC.sqrt rho) =
      CFC.sqrt rho * (Y1 * Y2) * CFC.sqrt rho := by
  classical
  let Q : Mat := Kraus.stationaryProj hrho
  obtain ⟨n, V, hV, hVrange⟩ :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).exists_range_isometry
  let T' : Matrix (Fin n) (Fin n) Complex →ₗ[Complex]
      Matrix (Fin n) (Fin n) Complex := stationarySupportCompression T V
  have hT'pos : IsPositiveMap T' :=
    stationarySupportCompression_isPositiveMap hT V
  have hT'tp : IsTracePreservingMap T' :=
    stationarySupportCompression_isTracePreservingMap
      hT hTP hrho hrhoFix V hV hVrange
  have hT'Schwarz : IsSchwarzMap (Matrix.traceAdjointMap T') := by
    simpa only [T'] using
      hSchwarz.traceAdjointMap_stationarySupportCompression hT V hV
  let sigma : Matrix (Fin n) (Fin n) Complex := Vᴴ * rho * V
  have hsigmaPosDef : sigma.PosDef := by
    have h := Matrix.PosSemidef.compression_on_support_posDef
      (D := D) (ρ := rho) hrho (k := n) (V := Vᴴ)
      (by simpa [Matrix.conjTranspose_conjTranspose] using hV)
      (by simpa [Q, Kraus.stationaryProj,
        Matrix.conjTranspose_conjTranspose] using hVrange)
    simpa [sigma, Matrix.conjTranspose_conjTranspose] using h
  have hrhoSupport : Q * rho * Q = rho := by
    simp only [Q]
    rw [Kraus.stationaryProj_mul hrho, Kraus.mul_stationaryProj hrho]
  have hsigmaFix : T' sigma = sigma := by
    change Vᴴ * T (V * (Vᴴ * rho * V) * Vᴴ) * V = Vᴴ * rho * V
    rw [show V * (Vᴴ * rho * V) * Vᴴ = rho by
      calc
        V * (Vᴴ * rho * V) * Vᴴ = (V * Vᴴ) * rho * (V * Vᴴ) := by
          simp only [Matrix.mul_assoc]
        _ = Q * rho * Q := by rw [hVrange]
        _ = rho := hrhoSupport,
      hrhoFix]
  have hsqrt : CFC.sqrt sigma = Vᴴ * CFC.sqrt rho * V := by
    simpa only [sigma] using Kraus.cfc_sqrt_compression hrho hVrange
  have hQidem : Q * Q = Q :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).2
  have hQY1 : Q * Y1 = Y1 := by
    conv_lhs => rw [← hY1mem]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQidem]
    exact hY1mem
  have hY1Q : Y1 * Q = Y1 := by
    conv_lhs => rw [← hY1mem]
    rw [Matrix.mul_assoc, hQidem]
    exact hY1mem
  have hY2Q : Y2 * Q = Y2 := by
    conv_lhs => rw [← hY2mem]
    rw [Matrix.mul_assoc, hQidem]
    exact hY2mem
  have hprodmem : Q * (Y1 * Y2) * Q = Y1 * Y2 := by
    calc
      Q * (Y1 * Y2) * Q = (Q * Y1) * (Y2 * Q) := by
        simp only [Matrix.mul_assoc]
      _ = Y1 * Y2 := by rw [hQY1, hY2Q]
  have htransport (Y : Mat) (hYmem : Q * Y * Q = Y) :
      CFC.sqrt sigma * (Vᴴ * Y * V) * CFC.sqrt sigma =
        Vᴴ * (CFC.sqrt rho * Y * CFC.sqrt rho) * V := by
    rw [hsqrt]
    calc
      (Vᴴ * CFC.sqrt rho * V) * (Vᴴ * Y * V) *
          (Vᴴ * CFC.sqrt rho * V) =
          Vᴴ * (CFC.sqrt rho * ((V * Vᴴ) * Y * (V * Vᴴ)) *
            CFC.sqrt rho) * V := by
        simp only [Matrix.mul_assoc]
      _ = Vᴴ * (CFC.sqrt rho * (Q * Y * Q) * CFC.sqrt rho) * V := by
        rw [hVrange]
      _ = Vᴴ * (CFC.sqrt rho * Y * CFC.sqrt rho) * V := by rw [hYmem]
  have hcompressWeighted (Y : Mat) (hYmem : Q * Y * Q = Y)
      (hYfix : T (CFC.sqrt rho * Y * CFC.sqrt rho) =
        CFC.sqrt rho * Y * CFC.sqrt rho) :
      T' (CFC.sqrt sigma * (Vᴴ * Y * V) * CFC.sqrt sigma) =
        CFC.sqrt sigma * (Vᴴ * Y * V) * CFC.sqrt sigma := by
    let W : Mat := CFC.sqrt rho * Y * CFC.sqrt rho
    have hWmem : Q * W * Q = W := by
      simpa only [Q, W] using Kraus.sqrt_conj_supported hrho Y
    have hVWV : V * (Vᴴ * W * V) * Vᴴ = W := by
      calc
        V * (Vᴴ * W * V) * Vᴴ = (V * Vᴴ) * W * (V * Vᴴ) := by
          simp only [Matrix.mul_assoc]
        _ = Q * W * Q := by rw [hVrange]
        _ = W := hWmem
    rw [htransport Y hYmem]
    change Vᴴ * T (V * (Vᴴ * W * V) * Vᴴ) * V = Vᴴ * W * V
    rw [hVWV, show T W = W by simpa only [W] using hYfix]
  have hcompressedMul := weightedFixed_mul_of_posDef
    hT'pos hT'tp hT'Schwarz hsigmaPosDef hsigmaFix
    (hcompressWeighted Y1 (by simpa only [Q] using hY1mem) hY1)
    (hcompressWeighted Y2 (by simpa only [Q] using hY2mem) hY2)
  have hcompressedProduct :
      (Vᴴ * Y1 * V) * (Vᴴ * Y2 * V) = Vᴴ * (Y1 * Y2) * V := by
    calc
      (Vᴴ * Y1 * V) * (Vᴴ * Y2 * V) =
          Vᴴ * (Y1 * (V * Vᴴ) * Y2) * V := by
        simp only [Matrix.mul_assoc]
      _ = Vᴴ * (Y1 * Q * Y2) * V := by rw [hVrange]
      _ = Vᴴ * (Y1 * Y2) * V := by rw [hY1Q]
  rw [hcompressedProduct, htransport (Y1 * Y2) hprodmem] at hcompressedMul
  let W : Mat := CFC.sqrt rho * (Y1 * Y2) * CFC.sqrt rho
  have hWmem : Q * W * Q = W := by
    simpa only [Q, W] using Kraus.sqrt_conj_supported hrho (Y1 * Y2)
  have hVWV : V * (Vᴴ * W * V) * Vᴴ = W := by
    calc
      V * (Vᴴ * W * V) * Vᴴ = (V * Vᴴ) * W * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = Q * W * Q := by rw [hVrange]
      _ = W := hWmem
  calc
    T W = T (V * (Vᴴ * W * V) * Vᴴ) := congrArg T hVWV.symm
    _ = V * T' (Vᴴ * W * V) * Vᴴ :=
      stationarySupportCompression_intertwine
        hT hrho hrhoFix V hV hVrange (Vᴴ * W * V)
    _ = V * (Vᴴ * W * V) * Vᴴ := by rw [hcompressedMul]
    _ = W := hVWV

/-- Weighted fixed points on the support of a stationary positive matrix form
a star-subalgebra of the existing corner algebra.  This support-correct form
includes the zero-support case: then the corner is the zero algebra. -/
noncomputable def weightedCornerFixedPointsStarSubalgebra
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosSemidef) (hrhoFix : T rho = rho) :
    letI hQ : IsIdempotentElem (Kraus.stationaryProj hrho) :=
      (Kraus.isOrthogonalProjection_stationaryProj hrho).2
    letI : Semiring hQ.Corner := instSemiringCorner _ hQ
    letI : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarModule Complex hQ.Corner :=
      MatrixCorner.cornerStarModuleComplex hQ
        (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    StarSubalgebra Complex hQ.Corner :=
  letI hQ : IsIdempotentElem (Kraus.stationaryProj hrho) :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).2
  let _ : Semiring hQ.Corner := instSemiringCorner _ hQ
  let _ : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
  let _ : Star hQ.Corner := MatrixCorner.cornerStar hQ
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let _ : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let _ : StarModule Complex hQ.Corner :=
    MatrixCorner.cornerStarModuleComplex hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let Q : Mat := Kraus.stationaryProj hrho
  have hSstar : (CFC.sqrt rho)ᴴ = CFC.sqrt rho :=
    Matrix.conjTranspose_cfc_sqrt rho
  have hSrhoS : CFC.sqrt rho * Q * CFC.sqrt rho = rho := by
    simpa only [Q] using (show
      CFC.sqrt rho * Kraus.stationaryProj hrho * CFC.sqrt rho = rho by
        rw [Kraus.cfc_sqrt_mul_stationaryProj hrho,
          CFC.sqrt_mul_sqrt_self rho hrho.nonneg])
  { carrier := {Y : hQ.Corner |
      T (CFC.sqrt rho * Y.1 * CFC.sqrt rho) =
        CFC.sqrt rho * Y.1 * CFC.sqrt rho}
    zero_mem' := by
      change T (CFC.sqrt rho * (0 : Mat) * CFC.sqrt rho) =
        CFC.sqrt rho * (0 : Mat) * CFC.sqrt rho
      simp
    add_mem' := by
      intro X Y hX hY
      change T (CFC.sqrt rho * (X.1 + Y.1) * CFC.sqrt rho) =
        CFC.sqrt rho * (X.1 + Y.1) * CFC.sqrt rho
      rw [Matrix.mul_add, Matrix.add_mul, T.map_add, hX, hY]
    one_mem' := by
      change T (CFC.sqrt rho * Q * CFC.sqrt rho) =
        CFC.sqrt rho * Q * CFC.sqrt rho
      rw [hSrhoS]
      exact hrhoFix
    mul_mem' := by
      intro X Y hX hY
      change T (CFC.sqrt rho * (X.1 * Y.1) * CFC.sqrt rho) =
        CFC.sqrt rho * (X.1 * Y.1) * CFC.sqrt rho
      have hXmem : Q * X.1 * Q = X.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp X.2
        rw [Matrix.mul_assoc, hR, hL]
      have hYmem : Q * Y.1 * Q = Y.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp Y.2
        rw [Matrix.mul_assoc, hR, hL]
      exact weightedCornerFixed_mul
        hT hTP hSchwarz hrho hrhoFix hXmem hYmem hX hY
    algebraMap_mem' := by
      intro c
      change T (CFC.sqrt rho * (c • Q) * CFC.sqrt rho) =
        CFC.sqrt rho * (c • Q) * CFC.sqrt rho
      have hsmul : CFC.sqrt rho * (c • Q) * CFC.sqrt rho = c • rho := by
        rw [Matrix.mul_smul, Matrix.smul_mul, hSrhoS]
      rw [hsmul, T.map_smul, hrhoFix]
    star_mem' := by
      intro Y hY
      change T (CFC.sqrt rho * Y.1ᴴ * CFC.sqrt rho) =
        CFC.sqrt rho * Y.1ᴴ * CFC.sqrt rho
      have hconj : CFC.sqrt rho * Y.1ᴴ * CFC.sqrt rho =
          (CFC.sqrt rho * Y.1 * CFC.sqrt rho)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hSstar, Matrix.mul_assoc]
      rw [hconj, hT.map_conjTranspose, hY] }

/-- Membership in the support-correct source-general weighted fixed-point
star-subalgebra is exactly the square-root sandwich fixed-point condition. -/
@[simp] theorem mem_weightedCornerFixedPointsStarSubalgebra
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosSemidef) (hrhoFix : T rho = rho)
    (hQ : IsIdempotentElem (Kraus.stationaryProj hrho) :=
      (Kraus.isOrthogonalProjection_stationaryProj hrho).2)
    (Y : hQ.Corner) :
    letI : Semiring hQ.Corner := instSemiringCorner _ hQ
    letI : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarModule Complex hQ.Corner :=
      MatrixCorner.cornerStarModuleComplex hQ
        (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    Y ∈ weightedCornerFixedPointsStarSubalgebra
      hT hTP hSchwarz hrho hrhoFix ↔
      T (CFC.sqrt rho * Y.1 * CFC.sqrt rho) =
        CFC.sqrt rho * Y.1 * CFC.sqrt rho :=
  Iff.rfl

/-! ## Wolf Corollary 6.7: the displayed inverse-square-root set -/

private theorem cfc_sqrt_mul_supportInvSqrt
    {rho : Mat} (hrho : rho.PosSemidef) :
    CFC.sqrt rho * hrho.supportInvSqrt = Kraus.stationaryProj hrho := by
  have hsqrt : CFC.sqrt rho = hrho.isHermitian.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt rho hrho.nonneg, cfcₙ_eq_cfc,
      hrho.isHermitian.cfc_eq]
  simpa only [hsqrt, Kraus.stationaryProj] using
    hrho.cfc_sqrt_mul_supportInvSqrt

private theorem supportInvSqrt_mul_cfc_sqrt
    {rho : Mat} (hrho : rho.PosSemidef) :
    hrho.supportInvSqrt * CFC.sqrt rho = Kraus.stationaryProj hrho := by
  have hsqrt : CFC.sqrt rho = hrho.isHermitian.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt rho hrho.nonneg, cfcₙ_eq_cfc,
      hrho.isHermitian.cfc_eq]
  simpa only [hsqrt, Kraus.stationaryProj] using
    hrho.supportInvSqrt_mul_cfc_sqrt

/-- On matrices supported by `rho`, conjugation by the support inverse square
root is inverse to conjugation by the square root.  This is the auxiliary
support identity used to identify Wolf's displayed set exactly. -/
private theorem sqrt_conj_supportInvSqrt_conj_eq
    {rho X : Mat} (hrho : rho.PosSemidef)
    (hX : Kraus.stationaryProj hrho * X *
      Kraus.stationaryProj hrho = X) :
    CFC.sqrt rho * (hrho.supportInvSqrt * X * hrho.supportInvSqrt) *
        CFC.sqrt rho = X := by
  calc
    CFC.sqrt rho * (hrho.supportInvSqrt * X * hrho.supportInvSqrt) *
        CFC.sqrt rho =
        (CFC.sqrt rho * hrho.supportInvSqrt) * X *
          (hrho.supportInvSqrt * CFC.sqrt rho) := by
            simp only [Matrix.mul_assoc]
    _ = Kraus.stationaryProj hrho * X * Kraus.stationaryProj hrho := by
      rw [cfc_sqrt_mul_supportInvSqrt hrho,
        supportInvSqrt_mul_cfc_sqrt hrho]
    _ = X := hX

/-- Conversely, on the support corner, conjugation by the support inverse
square root recovers the corner element from its square-root sandwich. -/
private theorem supportInvSqrt_conj_sqrt_conj_eq
    {rho Y : Mat} (hrho : rho.PosSemidef)
    (hY : Kraus.stationaryProj hrho * Y *
      Kraus.stationaryProj hrho = Y) :
    hrho.supportInvSqrt * (CFC.sqrt rho * Y * CFC.sqrt rho) *
        hrho.supportInvSqrt = Y := by
  calc
    hrho.supportInvSqrt * (CFC.sqrt rho * Y * CFC.sqrt rho) *
        hrho.supportInvSqrt =
        (hrho.supportInvSqrt * CFC.sqrt rho) * Y *
          (CFC.sqrt rho * hrho.supportInvSqrt) := by
            simp only [Matrix.mul_assoc]
    _ = Kraus.stationaryProj hrho * Y * Kraus.stationaryProj hrho := by
      rw [supportInvSqrt_mul_cfc_sqrt hrho,
        cfc_sqrt_mul_supportInvSqrt hrho]
    _ = Y := hY

/-- A fixed point supported by `rho` is the square-root sandwich of its
support-inverse-square-root conjugate.  This is source-general: it uses no
Kraus representation or complete positivity. -/
private theorem exists_weightedCorner_sqrt_eq_of_fixedPoint
    {T : Mat →ₗ[Complex] Mat}
    {rho : Mat} (hrho : rho.PosSemidef)
    {X : Mat} (hXFix : T X = X)
    (hXSupport : Kraus.stationaryProj hrho * X *
      Kraus.stationaryProj hrho = X) :
    ∃ Y : Mat,
      Kraus.stationaryProj hrho * Y * Kraus.stationaryProj hrho = Y ∧
      T (CFC.sqrt rho * Y * CFC.sqrt rho) =
        CFC.sqrt rho * Y * CFC.sqrt rho ∧
      CFC.sqrt rho * Y * CFC.sqrt rho = X := by
  let Y := hrho.supportInvSqrt * X * hrho.supportInvSqrt
  have hQInvLeft : Kraus.stationaryProj hrho * hrho.supportInvSqrt =
      hrho.supportInvSqrt := by
    simpa only [Kraus.stationaryProj] using
      hrho.supportProj_mul_supportInvSqrt
  have hInvQRight : hrho.supportInvSqrt * Kraus.stationaryProj hrho =
      hrho.supportInvSqrt := by
    simpa only [Kraus.stationaryProj] using
      hrho.supportInvSqrt_mul_supportProj
  have hYSupport : Kraus.stationaryProj hrho * Y *
      Kraus.stationaryProj hrho = Y := by
    dsimp only [Y]
    calc
      Kraus.stationaryProj hrho *
          (hrho.supportInvSqrt * X * hrho.supportInvSqrt) *
          Kraus.stationaryProj hrho =
          (Kraus.stationaryProj hrho * hrho.supportInvSqrt) * X *
            (hrho.supportInvSqrt * Kraus.stationaryProj hrho) := by
              simp only [Matrix.mul_assoc]
      _ = hrho.supportInvSqrt * X * hrho.supportInvSqrt := by
        rw [hQInvLeft, hInvQRight]
  have hSandwich : CFC.sqrt rho * Y * CFC.sqrt rho = X := by
    exact sqrt_conj_supportInvSqrt_conj_eq hrho hXSupport
  exact ⟨Y, hYSupport, by rw [hSandwich]; exact hXFix, hSandwich⟩

/-- At every maximum-rank stationary density, every fixed point is reached by
the weighted support corner.  The `every maximum rank` premise is stated by
quantifying an arbitrary `rho` whose rank bounds every stationary density. -/
theorem exists_weightedCorner_sqrt_eq_of_maximalRank
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    {rho : Mat} (hrho : rho.PosSemidef) (hrhoFix : T rho = rho)
    (hrhoMax : ∀ sigma : Mat, sigma.PosSemidef → sigma.trace = 1 →
      T sigma = sigma → sigma.rank ≤ rho.rank)
    {X : Mat} (hXFix : T X = X) :
    ∃ Y : Mat,
      Kraus.stationaryProj hrho * Y * Kraus.stationaryProj hrho = Y ∧
      T (CFC.sqrt rho * Y * CFC.sqrt rho) =
        CFC.sqrt rho * Y * CFC.sqrt rho ∧
      CFC.sqrt rho * Y * CFC.sqrt rho = X :=
  exists_weightedCorner_sqrt_eq_of_fixedPoint hrho hXFix
    (hT.maximalSupport_of_maximalRank hTP hrho hrhoFix hrhoMax X hXFix)

/-- Membership in the formal star-algebra is exactly membership in Wolf's
displayed set
`rho^(-1/2) {X | T X = X} rho^(-1/2)`, with the inverse square root
totalized to zero off `supp(rho)`. -/
theorem mem_weightedCornerFixedPointsStarSubalgebra_iff_inverseSandwich
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosSemidef) (_hrhoTrace : rho.trace = 1)
    (hrhoFix : T rho = rho)
    (hrhoMax : ∀ sigma : Mat, sigma.PosSemidef → sigma.trace = 1 →
      T sigma = sigma → sigma.rank ≤ rho.rank)
    (hQ : IsIdempotentElem (Kraus.stationaryProj hrho) :=
      (Kraus.isOrthogonalProjection_stationaryProj hrho).2)
    (Y : hQ.Corner) :
    letI : Semiring hQ.Corner := instSemiringCorner _ hQ
    letI : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarModule Complex hQ.Corner :=
      MatrixCorner.cornerStarModuleComplex hQ
        (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    Y ∈ weightedCornerFixedPointsStarSubalgebra
        hT hTP hSchwarz hrho hrhoFix ↔
      ∃ X : Mat, T X = X ∧
        Y.1 = hrho.supportInvSqrt * X * hrho.supportInvSqrt := by
  let _ : Semiring hQ.Corner := instSemiringCorner _ hQ
  let _ : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
  let _ : Star hQ.Corner := MatrixCorner.cornerStar hQ
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let _ : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let _ : StarModule Complex hQ.Corner :=
    MatrixCorner.cornerStarModuleComplex hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  have hYSupport : Kraus.stationaryProj hrho * Y.1 *
      Kraus.stationaryProj hrho = Y.1 := by
    obtain ⟨hLeft, hRight⟩ := (Subsemigroup.mem_corner_iff hQ).mp Y.2
    rw [Matrix.mul_assoc, hRight, hLeft]
  constructor
  · intro hYFixed
    let X : Mat := CFC.sqrt rho * Y.1 * CFC.sqrt rho
    refine ⟨X, ?_, ?_⟩
    · have hYFixed' :=
        (mem_weightedCornerFixedPointsStarSubalgebra
          hT hTP hSchwarz hrho hrhoFix hQ Y).mp hYFixed
      simpa only [X] using hYFixed'
    · exact (supportInvSqrt_conj_sqrt_conj_eq hrho hYSupport).symm
  · rintro ⟨X, hXFix, hYeq⟩
    have hXSupport :=
      hT.maximalSupport_of_maximalRank hTP hrho hrhoFix hrhoMax X hXFix
    have hSandwich := sqrt_conj_supportInvSqrt_conj_eq hrho hXSupport
    change T (CFC.sqrt rho * Y.1 * CFC.sqrt rho) =
      CFC.sqrt rho * Y.1 * CFC.sqrt rho
    rw [hYeq, hSandwich]
    exact hXFix

/-- **Wolf Corollary 6.7.** Let `T` be positive and trace preserving, with
Schwarz trace adjoint.  For every maximum-rank stationary density `rho`, the
support-inverse-square-root conjugate of the fixed-point space is a
star-algebra.  The returned carrier is identified exactly with Wolf's
displayed set; no ambient invertibility of `rho` is assumed. -/
theorem wolfCorollary67
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {rho : Mat} (hrho : rho.PosSemidef) (hrhoTrace : rho.trace = 1)
    (hrhoFix : T rho = rho)
    (hrhoMax : ∀ sigma : Mat, sigma.PosSemidef → sigma.trace = 1 →
      T sigma = sigma → sigma.rank ≤ rho.rank) :
    letI hQ : IsIdempotentElem (Kraus.stationaryProj hrho) :=
      (Kraus.isOrthogonalProjection_stationaryProj hrho).2
    letI : Semiring hQ.Corner := instSemiringCorner _ hQ
    letI : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    letI : StarModule Complex hQ.Corner :=
      MatrixCorner.cornerStarModuleComplex hQ
        (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
    ∃ A : StarSubalgebra Complex hQ.Corner,
      ∀ Y : hQ.Corner, Y ∈ A ↔
        ∃ X : Mat, T X = X ∧
          Y.1 = hrho.supportInvSqrt * X * hrho.supportInvSqrt := by
  let hQ : IsIdempotentElem (Kraus.stationaryProj hrho) :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).2
  let _ : Semiring hQ.Corner := instSemiringCorner _ hQ
  let _ : Algebra Complex hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
  let _ : Star hQ.Corner := MatrixCorner.cornerStar hQ
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let _ : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  let _ : StarModule Complex hQ.Corner :=
    MatrixCorner.cornerStarModuleComplex hQ
      (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  refine ⟨weightedCornerFixedPointsStarSubalgebra
    hT hTP hSchwarz hrho hrhoFix, ?_⟩
  intro Y
  exact mem_weightedCornerFixedPointsStarSubalgebra_iff_inverseSandwich
    hT hTP hSchwarz hrho hrhoTrace hrhoFix hrhoMax hQ Y

end IsPositiveMap
