/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectionQuadraticBound
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Removing a compressed exponential from a commuting product

A Hermitian exponential preserves a Hermitian fixed subspace when its
generator commutes with the defining matrix. On that subspace, a compressed
upper bound for a second exponential controls the exponential of the sum.
The proof applies the compressed bound to the vector after half of the
first exponential. It does not move a projection through an unrelated
operator.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 454--480,
`comparator:whole-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- A compressed exponential bound controls the corresponding commuting
exponential quadratic form on its fixed subspace. Idempotence of `P`,
Hermitianity of `B`, and positivity of the scalar are unnecessary for this implication.
Source: `07-comparators.tex`, lines 454--480. -/
theorem IsHermitian.re_dotProduct_exp_add_le_of_compressed_exp_le_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n ℂ} (hA : A.IsHermitian) (hP : P.IsHermitian)
    (hAP : Commute A P) (hAB : Commute A B)
    {c : ℝ} (hbound : P * NormedSpace.exp B * P ≤ c • P)
    {v : n → ℂ} (hv : P *ᵥ v = v) :
    (star v ⬝ᵥ (NormedSpace.exp (A + B) *ᵥ v)).re ≤
      c * (star v ⬝ᵥ (NormedSpace.exp A *ᵥ v)).re := by
  let C := NormedSpace.exp ((1 / 2 : ℝ) • A)
  have hC : C.IsHermitian :=
    (hA.smul (show IsSelfAdjoint (1 / 2 : ℝ) by
      simp [isSelfAdjoint_iff])).isSelfAdjoint.exp.isHermitian
  have hCP : Commute C P := (hAP.smul_left (1 / 2 : ℝ)).exp_left
  have hw : P *ᵥ (C *ᵥ v) = C *ᵥ v := by
    rw [mulVec_mulVec, ← hCP.eq, ← mulVec_mulVec, hv]
  have h := hP.re_dotProduct_mulVec_le_of_compression_le hbound hw
  have hCC : C * C = NormedSpace.exp A := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((1 / 2 : ℝ) • A))]
    congr 1
    rw [← add_smul]
    norm_num
  have hCB : Commute C (NormedSpace.exp B) :=
    (hAB.smul_left (1 / 2 : ℝ)).exp
  have hCBC : C * NormedSpace.exp B * C = NormedSpace.exp (A + B) := by
    rw [mul_assoc, ← hCB.eq, ← mul_assoc, hCC,
      ← Matrix.exp_add_of_commute _ _ hAB]
  have hleft : star (C *ᵥ v) ⬝ᵥ (NormedSpace.exp B *ᵥ (C *ᵥ v)) =
      star v ⬝ᵥ (NormedSpace.exp (A + B) *ᵥ v) := by
    rw [hC.star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, hCBC]
  have hright : star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) =
      star v ⬝ᵥ (NormedSpace.exp A *ᵥ v) := by
    rw [hC.star_mulVec_dotProduct, mulVec_mulVec, hCC]
  simpa only [hleft, hright] using h

/-- A compressed exponential contraction may be removed from a commuting
exponential quadratic form on its fixed subspace.
Source: `07-comparators.tex`, lines 454--480. -/
theorem IsHermitian.re_dotProduct_exp_add_le_of_compressed_exp_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n ℂ} (hA : A.IsHermitian) (hP : P.IsHermitian)
    (hAP : Commute A P) (hAB : Commute A B)
    (hbound : P * NormedSpace.exp B * P ≤ P)
    {v : n → ℂ} (hv : P *ᵥ v = v) :
    (star v ⬝ᵥ (NormedSpace.exp (A + B) *ᵥ v)).re ≤
      (star v ⬝ᵥ (NormedSpace.exp A *ᵥ v)).re := by
  simpa only [one_mul] using
    hA.re_dotProduct_exp_add_le_of_compressed_exp_le_smul hP hAP hAB
      (c := 1) (by simpa only [one_smul] using hbound) hv

/-- The vector comparison gives a compressed operator bound on a commuting
orthogonal projection range. Source: `07-comparators.tex`, lines 454--493. -/
theorem IsHermitian.compression_exp_add_le_of_compressed_exp_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hP : IsStarProjection P) (hAP : Commute A P) (hAB : Commute A B)
    {c : ℝ} (hbound : P * NormedSpace.exp B * P ≤ c • P) :
    P * NormedSpace.exp (A + B) * P ≤ c • (P * NormedSpace.exp A * P) := by
  have hPH : P.IsHermitian := hP.isSelfAdjoint.isHermitian
  have hEA : (NormedSpace.exp A).IsHermitian := hA.isSelfAdjoint.exp.isHermitian
  have hEAB : (NormedSpace.exp (A + B)).IsHermitian :=
    (hA.add hB).isSelfAdjoint.exp.isHermitian
  have hleft : (P * NormedSpace.exp (A + B) * P).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, hPH.eq, hEAB.eq, mul_assoc]
  have hright : (c • (P * NormedSpace.exp A * P)).IsHermitian := by
    simp only [IsHermitian, conjTranspose_smul, conjTranspose_mul,
      hPH.eq, hEA.eq, star_trivial, mul_assoc]
  have hdiff := hright.sub hleft
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hdiff
  intro v
  apply RCLike.nonneg_iff.mpr
  refine ⟨?_, hdiff.im_star_dotProduct_mulVec_self v⟩
  have hPv : P *ᵥ (P *ᵥ v) = P *ᵥ v := by
    rw [mulVec_mulVec, hP.isIdempotentElem.eq]
  have h := hA.re_dotProduct_exp_add_le_of_compressed_exp_le_smul
    hPH hAP hAB hbound hPv
  have hpair (X : Matrix n n ℂ) :
      star v ⬝ᵥ ((P * X * P) *ᵥ v) = star (P *ᵥ v) ⬝ᵥ (X *ᵥ (P *ᵥ v)) := by
    rw [hPH.star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]
  simpa only [sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec,
    dotProduct_smul, Complex.smul_re, smul_eq_mul, hpair, sub_nonneg] using h

/-- A positive density supported on the projection range obeys the same
exponential comparison. Its trace need not be one.
Source: `07-comparators.tex`, lines 454--493 and 513--555. -/
theorem IsHermitian.re_trace_mul_exp_add_le_of_compressed_exp_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B P ρ : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hP : IsStarProjection P) (hAP : Commute A P) (hAB : Commute A B)
    {c : ℝ} (hbound : P * NormedSpace.exp B * P ≤ c • P)
    (hρ : ρ.PosSemidef) (hPρ : P * ρ = ρ) :
    (ρ * NormedSpace.exp (A + B)).trace.re ≤
      c * (ρ * NormedSpace.exp A).trace.re := by
  have hPH : P.IsHermitian := hP.isSelfAdjoint.isHermitian
  have hρP : ρ * P = ρ := by
    have h := congrArg Matrix.conjTranspose hPρ
    simpa only [conjTranspose_mul, hPH.eq, hρ.isHermitian.eq] using h
  have htrace (X : Matrix n n ℂ) :
      (ρ * (P * X * P)).trace = (ρ * X).trace := by
    rw [← mul_assoc, ← mul_assoc, hρP, trace_mul_comm, ← mul_assoc, hPρ]
  have hoperator := hA.compression_exp_add_le_of_compressed_exp_le hB hP hAP hAB hbound
  have h := (RCLike.nonneg_iff.mp
    (hρ.trace_mul_nonneg (Matrix.le_iff.mp hoperator))).1
  simpa only [mul_sub, mul_smul_comm, trace_sub, trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul, htrace, sub_nonneg] using h

end Matrix
