/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.UnitarySchurTriangularization
import QICLean.Channel.Determinant.Basic
import QICLean.Channel.KrausRank
import QICLean.Channel.TransferMatrix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Positive determinant for completely positive maps of Kraus rank at most two

This file follows Wolf, Chapter 6, Proposition "Positive determinant for small
Kraus rank," and Equation (6.26).  For two Kraus operators `A, B`, the
repository's column-vectorization convention gives

`transferMatrix T = conj A ⊗ A + conj B ⊗ B`.

When `A` is invertible, this is factored using `A⁻¹ B`; unitary Schur
triangularization makes the conjugate pairing of the factors
`1 + conj λᵢ * λⱼ` explicit.  The singular case is obtained by the same
continuity/density step as in the source.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6,
  Proposition "Positive determinant for small Kraus rank," Equation (6.26),
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 496--517.
-/

open scoped Matrix Matrix.Norms.Frobenius BigOperators ComplexOrder Kronecker
open Matrix Finset

variable {D : ℕ}

/-! ## Determinant and transfer-matrix bridge -/

/-- The basis-independent channel determinant is the determinant of Wolf's
transfer matrix in the repository's column-vectorization convention. -/
theorem channelDet_eq_det_transferMatrix
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    channelDet T = Matrix.det (transferMatrix T) := by
  rw [channelDet_eq_linearMap_det]
  let e := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv
  calc
    LinearMap.det T = LinearMap.det (Matrix.frobeniusEuclideanMap T) := by
      rw [Matrix.frobeniusEuclideanMap_eq_conj]
      simpa only [e, LinearEquiv.conj_apply, LinearMap.comp_assoc] using
        (LinearMap.det_conj T e).symm
    _ = LinearMap.det (Matrix.toEuclideanLin (transferMatrix T)) := by
      rw [toEuclideanLin_transferMatrix]
    _ = Matrix.det (transferMatrix T) :=
      LinearMap.det_toLpLin 2 (transferMatrix T)

/-! ## Conjugate-pair determinant factors -/

/-- The finite product of Wolf's factors `1 + conj λᵢ * λⱼ` is
nonnegative.  The induction adds one diagonal factor and one product times its
complex conjugate. -/
private theorem prod_prod_one_add_star_mul_nonneg
    {I : Type*} (s : Finset I) (lam : I → ℂ) :
    0 ≤ (∏ i ∈ s, ∏ j ∈ s, (1 + star (lam i) * lam j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      let z : ℂ := ∏ j ∈ s, (1 + star (lam a) * lam j)
      have hcol : (∏ i ∈ s, (1 + star (lam i) * lam a)) = star z := by
        simp only [z, star_prod, star_add, star_one, star_mul, star_star]
      have hdiag : 0 ≤ 1 + star (lam a) * lam a :=
        add_nonneg zero_le_one (star_mul_self_nonneg (lam a))
      have hcross : 0 ≤ z * star z := mul_star_self_nonneg z
      rw [Finset.prod_insert ha]
      simp_rw [Finset.prod_insert ha]
      rw [Finset.prod_mul_distrib, hcol]
      change 0 ≤ (1 + star (lam a) * lam a) * z * (star z *
        ∏ i ∈ s, ∏ j ∈ s, (1 + star (lam i) * lam j))
      rw [mul_assoc, ← mul_assoc z]
      exact mul_nonneg hdiag (mul_nonneg hcross ih)

/-- For an upper-triangular matrix `R`, the determinant of Wolf's second
factor is the product of the conjugate-paired diagonal factors. -/
private theorem det_one_add_star_kronecker_self_nonneg_of_isUpperTriangular
    (R : Matrix (Fin D) (Fin D) ℂ) (hR : R.IsUpperTriangular) :
    0 ≤ Matrix.det (1 + R.map star ⊗ₖ R) := by
  classical
  let M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    1 + R.map star ⊗ₖ R
  let e : (Fin D × Fin D) ≃ (Fin D ×ₗ Fin D) := toLex
  have htri : (Matrix.reindex e e M).IsUpperTriangular := by
    intro i j hji
    change M (ofLex i) (ofLex j) = 0
    have hij : i ≠ j := ne_of_gt hji
    rcases Prod.Lex.lt_iff.mp hji with hfirst | ⟨hfirst, hsecond⟩
    · have hzero : R (ofLex i).1 (ofLex j).1 = 0 := hR hfirst
      simp [M, hij, hzero]
    · have hzero : R (ofLex i).2 (ofLex j).2 = 0 := hR hsecond
      simp [M, hij, hzero]
  rw [← Matrix.det_reindex_self e M, Matrix.det_of_isUpperTriangular htri]
  rw [← Equiv.prod_comp e]
  simp only [M, e, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.add_apply, Matrix.one_apply]
  rw [Fintype.prod_prod_type]
  exact prod_prod_one_add_star_mul_nonneg Finset.univ (fun i ↦ R i i)

/-- Unitary similarity does not change the determinant of Wolf's second
factor.  This is the transfer-matrix form of passing to Schur triangular
coordinates. -/
private theorem det_one_add_star_kronecker_self_eq_of_unitary_similarity
    (C U R : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hC : C = U * R * Uᴴ) :
    Matrix.det (1 + C.map star ⊗ₖ C) =
      Matrix.det (1 + R.map star ⊗ₖ R) := by
  classical
  let P : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := U.map star ⊗ₖ U
  have hUstar : U.map star ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    Matrix.map_star_mem_unitaryGroup_iff.mpr hU
  have hP : P ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ :=
    Matrix.kronecker_mem_unitary hUstar hU
  have hPPstar : P * Pᴴ = 1 := by
    simpa only [← Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hP)
  have hCmap : C.map star =
      (U.map star * R.map star) * (U.map star)ᴴ := by
    rw [hC]
    change (U * R * Uᴴ).map (starRingEnd ℂ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
  have hconj :
      (P * (R.map star ⊗ₖ R)) * Pᴴ = C.map star ⊗ₖ C := by
    calc
      (P * (R.map star ⊗ₖ R)) * Pᴴ =
          ((U.map star * R.map star) ⊗ₖ (U * R)) *
            ((U.map star)ᴴ ⊗ₖ Uᴴ) := by
              simp only [P, Matrix.conjTranspose_kronecker]
              rw [← Matrix.mul_kronecker_mul]
      _ = ((U.map star * R.map star) * (U.map star)ᴴ) ⊗ₖ
          ((U * R) * Uᴴ) := by
            rw [← Matrix.mul_kronecker_mul]
      _ = C.map star ⊗ₖ C := by
        rw [hCmap, hC]
  have hfactor :
      P * (1 + R.map star ⊗ₖ R) * Pᴴ = 1 + C.map star ⊗ₖ C := by
    rw [mul_add, mul_one, add_mul, hPPstar, hconj]
  have hdetP : Matrix.det P * star (Matrix.det P) = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using
      congrArg Matrix.det hPPstar
  calc
    Matrix.det (1 + C.map star ⊗ₖ C) =
        Matrix.det (P * (1 + R.map star ⊗ₖ R) * Pᴴ) := by rw [hfactor]
    _ = Matrix.det P * Matrix.det (1 + R.map star ⊗ₖ R) * star (Matrix.det P) := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    _ = Matrix.det P * star (Matrix.det P) *
        Matrix.det (1 + R.map star ⊗ₖ R) := by ring
    _ = Matrix.det (1 + R.map star ⊗ₖ R) := by rw [hdetP, one_mul]

/-- The determinant of Wolf's second factor is nonnegative. -/
private theorem det_one_add_star_kronecker_self_nonneg
    (C : Matrix (Fin D) (Fin D) ℂ) :
    0 ≤ Matrix.det (1 + C.map star ⊗ₖ C) := by
  obtain ⟨U, R, hR, hC, -⟩ := Matrix.exists_unitary_schur_triangularization C
  rw [det_one_add_star_kronecker_self_eq_of_unitary_similarity C U R U.property hC]
  exact det_one_add_star_kronecker_self_nonneg_of_isUpperTriangular R hR

/-- The determinant of the first factor in Equation (6.26) is a complex norm
square, hence nonnegative. -/
private theorem det_star_kronecker_self_nonneg
    (A : Matrix (Fin D) (Fin D) ℂ) :
    0 ≤ Matrix.det (A.map star ⊗ₖ A) := by
  rw [Matrix.det_kronecker]
  simp only [Fintype.card_fin]
  have hdetmap : Matrix.det (A.map star) = star (Matrix.det A) := by
    change Matrix.det (A.map (starRingEnd ℂ)) = (starRingEnd ℂ) (Matrix.det A)
    exact (RingHom.map_det (starRingEnd ℂ) A).symm
  rw [hdetmap]
  have hpow : star (Matrix.det A ^ D) = star (Matrix.det A) ^ D := by
    change (starRingEnd ℂ) (Matrix.det A ^ D) = (starRingEnd ℂ) (Matrix.det A) ^ D
    exact (starRingEnd ℂ).map_pow _ _
  rw [← hpow]
  exact star_mul_self_nonneg (Matrix.det A ^ D)

/-- Equation (6.26), in the repository's column-vectorization convention. -/
private theorem star_kronecker_add_eq_factor_of_det_ne_zero
    (A B : Matrix (Fin D) (Fin D) ℂ) (hA : Matrix.det A ≠ 0) :
    A.map star ⊗ₖ A + B.map star ⊗ₖ B =
      (A.map star ⊗ₖ A) *
        (1 + (A⁻¹ * B).map star ⊗ₖ (A⁻¹ * B)) := by
  have hAunit : IsUnit (Matrix.det A) := hA.isUnit
  have hcancel : A * (A⁻¹ * B) = B :=
    Matrix.mul_nonsing_inv_cancel_left A B hAunit
  have hcancelStar : A.map star * (A⁻¹ * B).map star = B.map star := by
    change A.map (starRingEnd ℂ) * (A⁻¹ * B).map (starRingEnd ℂ) =
      B.map (starRingEnd ℂ)
    rw [← Matrix.map_mul, hcancel]
  calc
    A.map star ⊗ₖ A + B.map star ⊗ₖ B =
        A.map star ⊗ₖ A +
          (A.map star * (A⁻¹ * B).map star) ⊗ₖ (A * (A⁻¹ * B)) := by
            rw [hcancel, hcancelStar]
    _ = A.map star ⊗ₖ A +
        (A.map star ⊗ₖ A) * ((A⁻¹ * B).map star ⊗ₖ (A⁻¹ * B)) := by
          rw [← Matrix.mul_kronecker_mul]
    _ = (A.map star ⊗ₖ A) *
        (1 + (A⁻¹ * B).map star ⊗ₖ (A⁻¹ * B)) := by
          rw [mul_add, mul_one]

/-- The two-Kraus transfer determinant is nonnegative when the first Kraus
operator is invertible. -/
private theorem det_two_kraus_transfer_nonneg_of_det_ne_zero_left
    (A B : Matrix (Fin D) (Fin D) ℂ) (hA : Matrix.det A ≠ 0) :
    0 ≤ Matrix.det (A.map star ⊗ₖ A + B.map star ⊗ₖ B) := by
  rw [star_kronecker_add_eq_factor_of_det_ne_zero A B hA, Matrix.det_mul]
  exact mul_nonneg (det_star_kronecker_self_nonneg A)
    (det_one_add_star_kronecker_self_nonneg (A⁻¹ * B))
