/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixSqrt

/-!
# Positive contractions relative to a singular reference

If `0 ≤ M ≤ ρ`, then `M * supportInv ρ * M ≤ M`, including when `ρ` is
singular and when the two matrices do not commute. Order also implies the
kernel inclusion and support absorption needed to reconstruct `M` from
its normalization by the inverse square root of `ρ`.

The sandwich inequality follows by expressing its difference as the sum of
two positive congruences. This uses only the generalized-inverse identity
`ρ⁺ * ρ * ρ⁺ = ρ⁺`; no inverse on the ambient space is required.

These are the matrix-order steps in the restoration construction of
*A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 417–446, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs here are independently written from the matrix APIs in QICLean
and Mathlib.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix.PosSemidef

variable {n : Type*} [Fintype n] {M ρ : Matrix n n ℂ}

/-- Positive-semidefinite order reverses kernel inclusion. In particular,
the support condition in the restoration construction follows from its
order hypothesis (`09-amplification.tex`, lines 417–446). -/
theorem mulVec_eq_zero_of_le (hM : M.PosSemidef) (hMρ : M ≤ ρ)
    (v : n → ℂ) (hv : ρ *ᵥ v = 0) : M *ᵥ v = 0 := by
  apply hM.dotProduct_mulVec_zero_iff.mp
  apply le_antisymm _ (hM.dotProduct_mulVec_nonneg v)
  have h := (Matrix.le_iff.mp hMρ).dotProduct_mulVec_nonneg v
  simpa only [Matrix.sub_mulVec, hv, zero_sub, dotProduct_neg, neg_nonneg] using h

variable [DecidableEq n]

/-- A positive matrix dominated by `ρ` is absorbed on the right by the
support projection of `ρ` (`09-amplification.tex`, lines 417–446). -/
theorem mul_supportProj_eq_self_of_le (hM : M.PosSemidef) (hρ : ρ.PosSemidef)
    (hMρ : M ≤ ρ) : M * hρ.supportProj = M :=
  hρ.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le
    (hM.mulVec_eq_zero_of_le hMρ)

/-- A positive matrix dominated by `ρ` is absorbed on the left by the
support projection of `ρ` (`09-amplification.tex`, lines 417–446). -/
theorem supportProj_mul_eq_self_of_le (hM : M.PosSemidef) (hρ : ρ.PosSemidef)
    (hMρ : M ≤ ρ) : hρ.supportProj * M = M := by
  simpa only [Matrix.conjTranspose_mul, hρ.supportProj_isHermitian.eq,
    hM.isHermitian.eq] using
    congrArg Matrix.conjTranspose (hM.mul_supportProj_eq_self_of_le hρ hMρ)

/-- Normalization by the support inverse square root sends `0 ≤ M ≤ ρ`
below the support projection of `ρ` (`09-amplification.tex`, lines 417–446). -/
theorem supportInvSqrt_mul_mul_supportInvSqrt_le_supportProj
    (hρ : ρ.PosSemidef) (hMρ : M ≤ ρ) :
    hρ.supportInvSqrt * M * hρ.supportInvSqrt ≤ hρ.supportProj := by
  have h := (Matrix.le_iff.mp hMρ).mul_mul_conjTranspose_same hρ.supportInvSqrt
  apply Matrix.le_iff.mpr
  simpa only [PosSemidef.supportProj, hρ.supportInvSqrt_isHermitian.eq,
    Matrix.mul_sub, Matrix.sub_mul,
    hρ.supportInvSqrt_mul_self_mul_supportInvSqrt] using h

/-- The difference between a matrix and its support-inverse sandwich is a
sum of two congruences. Positivity of the summands gives the singular
restoration bound in `09-amplification.tex`, lines 417–446. -/
theorem sub_mul_supportInv_mul_eq (hM : M.PosSemidef) (hρ : ρ.PosSemidef) :
    M - M * hρ.supportInv * M =
      (1 - M * hρ.supportInv) * M * (1 - M * hρ.supportInv)ᴴ +
        (M * hρ.supportInv) * (ρ - M) * (M * hρ.supportInv)ᴴ := by
  have hInv : hρ.supportInv * ρ * hρ.supportInv = hρ.supportInv := by
    rw [hρ.supportInv_mul_self]
    exact hρ.supportProj_mul_supportInv
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, hM.isHermitian.eq, hρ.supportInv_isHermitian.eq]
  calc
    M - M * hρ.supportInv * M =
        M - M * hρ.supportInv * M - M * hρ.supportInv * M +
          M * (hρ.supportInv * ρ * hρ.supportInv) * M := by
      rw [hInv]
      abel
    _ = _ := by noncomm_ring

/-- If `0 ≤ M ≤ ρ`, the support-inverse sandwich difference is positive
semidefinite. This is the singular matrix-order bound used in `09-amplification.tex`,
lines 417–446, with no full-rank or commutation hypothesis. -/
theorem sub_mul_supportInv_mul_posSemidef (hM : M.PosSemidef) (hρ : ρ.PosSemidef)
    (hMρ : M ≤ ρ) : (M - M * hρ.supportInv * M).PosSemidef := by
  rw [hM.sub_mul_supportInv_mul_eq hρ]
  exact (hM.mul_mul_conjTranspose_same (1 - M * hρ.supportInv)).add
    ((Matrix.le_iff.mp hMρ).mul_mul_conjTranspose_same (M * hρ.supportInv))

/-- If `0 ≤ M ≤ ρ`, then `M ρ⁺ M ≤ M`, with the inverse taken only on
the support of `ρ`. This is the sandwich bound in the restoration
construction of `09-amplification.tex`, lines 417–446. -/
theorem mul_supportInv_mul_le (hM : M.PosSemidef) (hρ : ρ.PosSemidef)
    (hMρ : M ≤ ρ) : M * hρ.supportInv * M ≤ M :=
  hM.sub_mul_supportInv_mul_posSemidef hρ hMρ

end Matrix.PosSemidef
