/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SupportInverseSandwich

/-!
# Weighted coefficient bounds for singular restoration

For a positive-semidefinite matrix bounded by a real diagonal reference,
the sum of squared coefficients weighted by the reciprocal diagonal
entries is the trace of the support-inverse sandwich. Restricting the
weighted index to any selected set can only decrease this sum. The other
index still ranges over the entire ambient space.

These are the coefficient and trace steps in the restoration construction
of *A two-dimensional area law from a global spectral gap*, Section 9,
`09-amplification.tex`, lines 417–446, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs here are independently written from the matrix APIs in QICLean
and Mathlib.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {M ρ : Matrix n n ℂ} {p : n → ℝ}

omit [Fintype n] in
/-- The real entries of a positive-semidefinite diagonal matrix are
nonnegative, including the entries outside its support. -/
theorem PosSemidef.nonneg_of_eq_diagonal (hρ : ρ.PosSemidef)
    (hdiag : ρ = diagonal (fun x ↦ (p x : ℂ))) (x : n) : 0 ≤ p x := by
  have h := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := x))).1
  simpa only [hdiag, diagonal_apply_eq, Complex.ofReal_re] using h

/-- The support inverse of a nonnegative real diagonal matrix is obtained
by taking reciprocals of its entries, with zero entries remaining zero. -/
theorem PosSemidef.supportInv_eq_diagonal (hρ : ρ.PosSemidef)
    (hdiag : ρ = diagonal (fun x ↦ (p x : ℂ))) :
    hρ.supportInv = diagonal (fun x ↦ (((p x)⁻¹ : ℝ) : ℂ)) := by
  have hsqrt : hρ.supportInvSqrt =
      diagonal (fun x ↦ (((Real.sqrt (p x))⁻¹ : ℝ) : ℂ)) := by
    rw [PosSemidef.supportInvSqrt, ← hρ.isHermitian.cfc_eq, hdiag,
      Matrix.cfc_diagonal p _ ((Set.finite_range p).continuousOn _)]
    congr 1
    funext x
    by_cases hx : p x = 0 <;> simp [hx]
  rw [PosSemidef.supportInv, hsqrt, diagonal_mul_diagonal]
  congr 1
  funext x
  rw [← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (hρ.nonneg_of_eq_diagonal hdiag x)]

private theorem trace_mul_diagonal_mul_re (hM : M.IsHermitian) (w : n → ℝ) :
    (trace (M * diagonal (fun x ↦ (w x : ℂ)) * M)).re =
      ∑ x, ∑ y, w x * ‖M y x‖ ^ 2 := by
  rw [trace_mul_cycle, trace_mul_comm (M * M)]
  simp only [trace, diag_apply, diagonal_mul]
  simp only [mul_apply, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hprod : M x y * M y x = ((‖M y x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hM.apply x y]
    simpa only [RCLike.star_def, Complex.ofReal_pow] using Complex.conj_mul' (M y x)
  rw [hprod, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The real trace of a support-inverse sandwich is the full weighted sum
of squared coefficients when the reference matrix is diagonal. Both sums
range over the complete ambient basis, including zero-probability indices.
Source: `09-amplification.tex`, lines 417–446. -/
theorem PosSemidef.trace_mul_supportInv_mul_re (hM : M.PosSemidef)
    (hρ : ρ.PosSemidef) (hdiag : ρ = diagonal (fun x ↦ (p x : ℂ))) :
    (trace (M * hρ.supportInv * M)).re =
      ∑ x, ∑ y, ‖M y x‖ ^ 2 / p x := by
  rw [hρ.supportInv_eq_diagonal hdiag, trace_mul_diagonal_mul_re hM.isHermitian]
  simp only [div_eq_mul_inv, mul_comm]

/-- Selecting some weighted columns only decreases the support-inverse
sandwich trace. The row index is unrestricted; no invertibility away from
the selected set is assumed. The inequality is also valid for selected
zero entries, since their reciprocal weights are zero.
Source: `09-amplification.tex`, lines 417–446. -/
theorem PosSemidef.selected_sum_sq_div_le_trace_mul_supportInv_mul
    (hM : M.PosSemidef) (hρ : ρ.PosSemidef)
    (hdiag : ρ = diagonal (fun x ↦ (p x : ℂ))) (E : Finset n) :
    (∑ x ∈ E, ∑ y, ‖M y x‖ ^ 2 / p x) ≤
      (trace (M * hρ.supportInv * M)).re := by
  rw [hM.trace_mul_supportInv_mul_re hρ hdiag]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
  intro x _ _
  exact Finset.sum_nonneg fun y _ ↦
    div_nonneg (sq_nonneg _) (hρ.nonneg_of_eq_diagonal hdiag x)

/-- The real trace of the singular support-inverse sandwich is at most
the original trace whenever `0 ≤ M ≤ ρ`.
Source: `09-amplification.tex`, lines 417–446. -/
theorem PosSemidef.trace_mul_supportInv_mul_re_le (hM : M.PosSemidef)
    (hρ : ρ.PosSemidef) (hMρ : M ≤ ρ) :
    (trace (M * hρ.supportInv * M)).re ≤ (trace M).re := by
  have h := (Complex.nonneg_iff.mp
    (hM.sub_mul_supportInv_mul_posSemidef hρ hMρ).trace_nonneg).1
  rw [trace_sub, Complex.sub_re] at h
  exact sub_nonneg.mp h

/-- The selected restoring coefficients obey the full trace chain for a
possibly singular diagonal reference. No full-rank or commutation
hypothesis is imposed, and the row sum uses the full ambient basis.
Source: `09-amplification.tex`, lines 417–446. -/
theorem PosSemidef.selected_sum_sq_div_le_trace (hM : M.PosSemidef)
    (hρ : ρ.PosSemidef) (hdiag : ρ = diagonal (fun x ↦ (p x : ℂ)))
    (hMρ : M ≤ ρ) (E : Finset n) :
    (∑ x ∈ E, ∑ y, ‖M y x‖ ^ 2 / p x) ≤
        (trace (M * hρ.supportInv * M)).re ∧
      (trace (M * hρ.supportInv * M)).re ≤ (trace M).re :=
  ⟨hM.selected_sum_sq_div_le_trace_mul_supportInv_mul hρ hdiag E,
    hM.trace_mul_supportInv_mul_re_le hρ hMρ⟩

end Matrix
