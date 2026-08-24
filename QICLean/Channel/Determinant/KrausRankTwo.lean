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

/-- The singular first-Kraus case follows by the density/continuity argument in
Wolf: add a scalar tending to zero, and use Schur coordinates to see that the
perturbed matrices are eventually invertible. -/
private theorem det_two_kraus_transfer_nonneg
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    0 ≤ Matrix.det (A.map star ⊗ₖ A + B.map star ⊗ₖ B) := by
  classical
  let ε : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1)
  let A' : ℕ → Matrix (Fin D) (Fin D) ℂ := fun n ↦ A + ε n • 1
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa only [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  have hA' : Filter.Tendsto A' Filter.atTop (nhds A) := by
    simpa only [A', zero_smul, add_zero] using
      tendsto_const_nhds.add (hε.smul_const (1 : Matrix (Fin D) (Fin D) ℂ))
  obtain ⟨U, R, hR, hA, -⟩ := Matrix.exists_unitary_schur_triangularization A
  let R' : ℕ → Matrix (Fin D) (Fin D) ℂ := fun n ↦ R + ε n • 1
  have hR'tri (n : ℕ) : (R' n).IsUpperTriangular := by
    apply hR.add
    intro i j hji
    have hij : i ≠ j := ne_of_gt hji
    simp [hij]
  have hR'diag : ∀ᶠ n in Filter.atTop, ∀ i, R' n i i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : R i i = 0
    · exact Filter.Eventually.of_forall fun n ↦ by
        have hden : (n : ℂ) + 1 ≠ 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n + 1 : ℕ) : ℂ) ≠ 0)
        simp [R', hi, ε, hden]
    · have ht : Filter.Tendsto (fun n ↦ R i i + ε n) Filter.atTop (nhds (R i i)) := by
        simpa only [add_zero] using tendsto_const_nhds.add hε
      simpa [R'] using ht.eventually_ne hi
  have hR'det : ∀ᶠ n in Filter.atTop, Matrix.det (R' n) ≠ 0 := by
    filter_upwards [hR'diag] with n hn
    rw [Matrix.det_of_isUpperTriangular (hR'tri n)]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hn i
  have hUUstar : (U : Matrix (Fin D) (Fin D) ℂ) *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
    simpa only [← Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.property)
  have hsimilar (n : ℕ) : A' n =
      (U : Matrix (Fin D) (Fin D) ℂ) * R' n *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
    simp [A', R', hA, mul_add, add_mul, Matrix.mul_assoc, hUUstar]
  have hUdet : Matrix.det (U : Matrix (Fin D) (Fin D) ℂ) ≠ 0 :=
    (Matrix.UnitaryGroup.det_isUnit U).ne_zero
  have hA'det : ∀ᶠ n in Filter.atTop, Matrix.det (A' n) ≠ 0 := by
    filter_upwards [hR'det] with n hn
    rw [hsimilar, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero hUdet hn) (by simpa using hUdet)
  have hcontinuous : Continuous (fun X : Matrix (Fin D) (Fin D) ℂ ↦
      Matrix.det (X.map star ⊗ₖ X + B.map star ⊗ₖ B)) := by
    have hstar : Continuous (fun X : Matrix (Fin D) (Fin D) ℂ ↦ X.map star) :=
      continuous_id.matrix_map continuous_star
    exact ((Continuous.matrix_kronecker hstar continuous_id).add continuous_const).matrix_det
  apply ge_of_tendsto (hcontinuous.continuousAt.tendsto.comp hA')
  exact hA'det.mono fun n hn ↦
    det_two_kraus_transfer_nonneg_of_det_ne_zero_left (A' n) B hn

/-! ## Wolf's small-Kraus-rank proposition -/

/-- **Wolf, Chapter 6, positive determinant for small Kraus rank (two-term
form).** A completely positive map displayed with two Kraus operators has
nonnegative determinant.  No trace-preservation hypothesis is used. -/
theorem channelDet_nonneg_of_two_kraus
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ)
    (hT : ∀ X, T X = A * X * Aᴴ + B * X * Bᴴ) :
    0 ≤ channelDet T := by
  let K : Fin 2 → Matrix (Fin D) (Fin D) ℂ := ![A, B]
  have hK : ∀ X, T X = ∑ i : Fin 2, K i * X * (K i)ᴴ := by
    intro X
    simpa [K, Fin.sum_univ_two] using hT X
  rw [channelDet_eq_det_transferMatrix,
    transferMatrix_kraus K T hK, Fin.sum_univ_two]
  simpa [K] using det_two_kraus_transfer_nonneg A B

/-- A map admitting a Kraus representation with at most two operators has
nonnegative determinant.  Ranks zero and one are included by the zero-padding
operation from Wolf, Theorem 2.1. -/
theorem channelDet_nonneg_of_hasKrausRankLE_two
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hRank : Channel.HasKrausRankLE T 2) :
    0 ≤ channelDet T := by
  rcases hRank with ⟨r, hr, hT⟩
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono hT hr
  exact channelDet_nonneg_of_two_kraus T (K 0) (K 1) fun X ↦ by
    simpa only [Fin.sum_univ_two] using hK X

/-- **Wolf, Chapter 6, positive determinant for small Kraus rank.** If a
completely positive map has Kraus rank (equivalently, Choi rank) at most two,
then its determinant is nonnegative.  This includes Kraus ranks zero and one
and does not assume trace preservation. -/
theorem IsKrausCP.channelDet_nonneg_of_choiRank_le_two
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hCP : IsKrausCP T) (hRank : Channel.choiRank T ≤ 2) :
    0 ≤ channelDet T := by
  exact channelDet_nonneg_of_hasKrausRankLE_two T
    ⟨Channel.choiRank T, hRank, Channel.hasKrausCard_choiRank_of_cp hCP⟩
