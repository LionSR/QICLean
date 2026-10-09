/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixAux
import Mathlib.Analysis.Matrix.Order

/-!
# Quadratic bounds for vectors fixed by a Hermitian compression

An operator upper bound after Hermitian compression gives the corresponding
quadratic-form bound on every vector fixed by the compressing matrix.
Idempotence of that matrix and commutation with the bounded operator are
unnecessary.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 481–493, `comparator:good-auxiliary`.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

/-- Matrix order implies order of the real quadratic forms on every vector.
Source: `07-comparators.tex`, lines 454–493. -/
theorem re_dotProduct_mulVec_le_of_le
    {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hAB : A ≤ B) (v : n → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).re ≤ (star v ⬝ᵥ (B *ᵥ v)).re := by
  have h := (RCLike.nonneg_iff.mp
    ((Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg v)).1
  simpa only [sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using h

/-- A compressed operator bound gives a quadratic-form bound on every
fixed vector. Source: `07-comparators.tex`, lines 481–493,
`comparator:good-auxiliary`. No idempotence or commutation is assumed. -/
theorem IsHermitian.re_dotProduct_mulVec_le_of_compression_le
    {n : Type*} [Fintype n] {P M : Matrix n n ℂ} (hP : P.IsHermitian)
    {c : ℝ} (hbound : P * M * P ≤ c • P) {v : n → ℂ} (hv : P *ᵥ v = v) :
    (star v ⬝ᵥ (M *ᵥ v)).re ≤ c * (star v ⬝ᵥ v).re := by
  have hquad : star v ⬝ᵥ ((P * M * P) *ᵥ v) = star v ⬝ᵥ (M *ᵥ v) := by
    rw [← mulVec_mulVec, hv, ← mulVec_mulVec,
      ← hP.star_mulVec_dotProduct, hv]
  have h := re_dotProduct_mulVec_le_of_le hbound v
  simpa only [smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul,
    hv, hquad] using h

/-- A change of finite orthonormal coordinates preserves the exact complex
quadratic form. Source: `07-comparators.tex`, lines 441–590. -/
theorem star_dotProduct_submatrix_equiv
    {n m : Type*} [Fintype n] [Fintype m]
    (H : Matrix n n ℂ) (e : n ≃ m) (w : m → ℂ) :
    star w ⬝ᵥ (H.submatrix e.symm e.symm *ᵥ w) =
      star (w ∘ e) ⬝ᵥ (H *ᵥ (w ∘ e)) := by
  simp only [submatrix_mulVec_equiv, dotProduct_comp_equiv_symm,
    Equiv.symm_symm, Function.comp_def, Pi.star_apply]

end Matrix
