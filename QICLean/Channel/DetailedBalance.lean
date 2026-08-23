/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Channel.SelfDual

/-!
# Detailed balance and transfer matrices

This file records the matrix identities at the start of Wolf's proof that
detailed balance controls the Jordan condition number.

## Main results

* `transferMatrix_detailedBalance`: Eq. (8.110) becomes
  `Σ̂ T̂ᴴ = T̂ Σ̂` in the transfer-matrix representation.
* `transferMatrix_sigmaSandwich_eq_kronecker_and_posDef`: the matrix
  representation of `X ↦ sqrt(sigma) X sqrt(sigma)` is the positive-definite
  Kronecker product used by Wolf.
* `Matrix.PosDef.inv_sqrt_mul_mul_sqrt_isHermitian_of_detailedBalance`: conjugating
  by the positive square root in the detailed-balance identity gives a
  Hermitian matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
  Proposition “Jordan condition number and detailed balance”][Wolf2012Quantum]
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker

variable {D : ℕ}

/-- Wolf Eq. (8.110) in the transfer-matrix representation:
`Σ ∘ T* = T ∘ Σ` implies `Σ̂ T̂† = T̂ Σ̂`.

The Hermiticity-preserving hypothesis is exactly the hypothesis used to
identify the transfer matrix of `T*` with `T̂†`.

Source: Wolf (2012), Chapter 8, Eq. (8.110) and lines 1288--1290 of
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`. -/
theorem transferMatrix_detailedBalance
    (T Sigma : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : ∀ X, T Xᴴ = (T X)ᴴ)
    (hdb : Sigma.comp (Matrix.traceAdjointMap T) = T.comp Sigma) :
    transferMatrix Sigma * (transferMatrix T)ᴴ =
      transferMatrix T * transferMatrix Sigma := by
  rw [transferMatrix_conjTranspose_eq_traceAdjointMap T hT,
    ← transferMatrix_comp, ← transferMatrix_comp, hdb]

/-- For positive-definite `sigma`, the transfer matrix of
`Sigma(X) = sqrt(sigma) X sqrt(sigma)` is
`conj(sqrt(sigma)) ⊗ sqrt(sigma)` and is positive definite.

This verifies the Kronecker/matrix-representation identity used in Wolf's
specialization rather than treating it as definitional.

Source: Wolf (2012), Chapter 8, proof of the proposition “Jordan condition
number and detailed balance”, lines 1291--1292 of
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`. -/
theorem transferMatrix_sigmaSandwich_eq_kronecker_and_posDef
    (sigma : Matrix (Fin D) (Fin D) ℂ) (hsigma : sigma.PosDef) :
    transferMatrix (unitaryConjLM (CFC.sqrt sigma)) =
        (CFC.sqrt sigma).map (starRingEnd ℂ) ⊗ₖ CFC.sqrt sigma ∧
      (transferMatrix (unitaryConjLM (CFC.sqrt sigma))).PosDef := by
  let R := CFC.sqrt sigma
  have hRpsd : R.PosSemidef := by
    simpa [R] using Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg sigma)
  have hRdet : IsUnit R.det := by
    simpa [R] using hsigma.isUnit_det_cfc_sqrt
  have hRpd : R.PosDef :=
    hRpsd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det R).2 hRdet)
  have hRmap : R.map (starRingEnd ℂ) = R.transpose := by
    ext i j
    have hij := congr_fun (congr_fun (Matrix.conjTranspose_cfc_sqrt sigma) j) i
    simpa [R, Matrix.conjTranspose_apply] using hij
  have hrep := transferMatrix_unitaryConj R
  refine ⟨by simpa [R] using hrep, ?_⟩
  rw [hrep, hRmap]
  exact hRpd.transpose.kronecker hRpd

/-- Wolf's fixed-point observation in the `Sigma(X) = sqrt(sigma) X sqrt(sigma)`
specialization.  Detailed balance and `T*(1) = 1` imply `T(sigma) = sigma`.

Source: Wolf (2012), Chapter 8, proposition “Jordan condition number and
detailed balance”, lines 1283--1285 of
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`. -/
theorem fixedPoint_of_detailedBalance_sigmaSandwich
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (sigma : Matrix (Fin D) (Fin D) ℂ) (hsigma : sigma.PosDef)
    (hTstar : Matrix.traceAdjointMap T 1 = 1)
    (hdb :
      (unitaryConjLM (CFC.sqrt sigma)).comp (Matrix.traceAdjointMap T) =
        T.comp (unitaryConjLM (CFC.sqrt sigma))) :
    T sigma = sigma := by
  have hsqrt : CFC.sqrt sigma * CFC.sqrt sigma = sigma :=
    CFC.sqrt_mul_sqrt_self sigma
  calc
    T sigma = T (CFC.sqrt sigma * CFC.sqrt sigma) := by rw [hsqrt]
    _ = T (unitaryConjLM (CFC.sqrt sigma) 1) := by
      rw [unitaryConjLM_apply, Matrix.mul_one, Matrix.conjTranspose_cfc_sqrt]
    _ = unitaryConjLM (CFC.sqrt sigma) (Matrix.traceAdjointMap T 1) := by
      exact (LinearMap.congr_fun hdb 1).symm
    _ = unitaryConjLM (CFC.sqrt sigma) 1 := by rw [hTstar]
    _ = CFC.sqrt sigma * CFC.sqrt sigma := by
      rw [unitaryConjLM_apply, Matrix.mul_one, Matrix.conjTranspose_cfc_sqrt]
    _ = sigma := hsqrt

namespace Matrix

/-- The square-root similarity in Wolf's detailed-balance argument is
Hermitian.  If `S > 0` and `S A† = A S`, then
`S⁻¹/² A S¹/²` is Hermitian.

Source: Wolf (2012), Chapter 8, proof of the proposition “Jordan condition
number and detailed balance”, lines 1288--1291 of
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`. -/
theorem PosDef.inv_sqrt_mul_mul_sqrt_isHermitian_of_detailedBalance
    {n : Type*} [Fintype n] [DecidableEq n]
    {S A : Matrix n n ℂ} (hS : S.PosDef) (hdb : S * Aᴴ = A * S) :
    ((CFC.sqrt S)⁻¹ * A * CFC.sqrt S).IsHermitian := by
  let R := CFC.sqrt S
  have hRstar : Rᴴ = R := by
    simpa [R] using Matrix.conjTranspose_cfc_sqrt S
  have hRdet : IsUnit R.det := by
    simpa [R] using hS.isUnit_det_cfc_sqrt
  have hRinvstar : (R⁻¹)ᴴ = R⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hRstar]
  have hRinv_mul : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hRmul_inv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRR : R * R = S := by
    simpa [R] using CFC.sqrt_mul_sqrt_self S
  have hcore : R * Aᴴ * R⁻¹ = R⁻¹ * A * R := by
    calc
      R * Aᴴ * R⁻¹ = R⁻¹ * (R * R) * Aᴴ * R⁻¹ := by
        rw [← Matrix.mul_assoc, hRinv_mul, Matrix.one_mul]
      _ = R⁻¹ * S * Aᴴ * R⁻¹ := by rw [hRR]
      _ = R⁻¹ * (S * Aᴴ) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (A * S) * R⁻¹ := by rw [hdb]
      _ = R⁻¹ * A * S * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ * A * R := by
        rw [← hRR]
        simp only [Matrix.mul_assoc, hRmul_inv, Matrix.mul_one]
  change ((R⁻¹ * A * R)ᴴ = R⁻¹ * A * R)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRstar, hRinvstar]
  simpa only [Matrix.mul_assoc] using hcore

end Matrix
