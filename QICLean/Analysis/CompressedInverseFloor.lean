/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# From a compressed inverse bound to a metric floor

Congruence by an invertible Hermitian matrix converts the bound on the
compressed inverse of its square into a lower bound for that square.
The idempotent commutes with the metric; no commutation with the later
pinning projection is asserted here.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  `07-comparators.tex`, lines 454–476 and 603–621.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Congruence converts the inverse comparison into the corresponding floor.
This is the finite-dimensional matrix step of the area-law lower comparison,
`07-comparators.tex`, lines 454–476 and 603–621. -/
theorem compressed_square_floor_of_inv_le
    (L S : Matrix n n ℂ) (hL : IsSelfAdjoint L) (hunit : IsUnit L)
    (hS : IsIdempotentElem S) (hLS : Commute L S)
    {B : ℝ} (hB : 0 < B)
    (hinv : S * (L ^ 2)⁻¹ * S ≤ B • S) :
    B⁻¹ • S ≤ S * (L ^ 2) * S := by
  have hdet : IsUnit L.det := (isUnit_iff_isUnit_det L).mp hunit
  have hcancel : L * (L ^ 2)⁻¹ * L = 1 := by
    simp only [pow_two, mul_inv_rev, ← mul_assoc, mul_nonsing_inv L hdet,
      one_mul, nonsing_inv_mul L hdet]
  have hcong := hL.conjugate_le_conjugate hinv
  have htriple (T : Matrix n n ℂ) :
      L * (S * T * S) * L = S * (L * T * L) * S := by
    calc
      _ = (L * S) * T * (S * L) := by simp only [mul_assoc]
      _ = (S * L) * T * (L * S) :=
        congrArg₂ (fun a b => a * T * b) hLS.eq hLS.symm.eq
      _ = S * (L * T * L) * S := by simp only [mul_assoc]
  have hright : L * S * L = S * (L ^ 2) * S := by
    simpa only [mul_one, hS.eq, pow_two] using htriple 1
  rw [htriple, hcancel, mul_one, hS.eq, mul_smul_comm, smul_mul_assoc, hright] at hcong
  simpa only [smul_smul, inv_mul_cancel₀ hB.ne', one_smul] using
    smul_le_smul_of_nonneg_left hcong (inv_pos.mpr hB).le

end Matrix
