/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.MatrixAux
import QICLean.Analysis.TraceNormVariational
import Mathlib.Algebra.Order.Chebyshev

/-!
# Trace-norm and Hilbert--Schmidt norm comparison

This file proves Wolf's finite-dimensional comparison between the Schatten one-norm and the
Hilbert--Schmidt norm,
`‖A‖₂ ≤ ‖A‖₁ ≤ √D * ‖A‖₂`.  The first inequality is the `p = 1`, `p' = 2`
case of Equation (8.1), and the second is the corresponding case of Equation (8.7).
They are used in the proof of convergence towards asymptotic states at source lines 1352 and 1358.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8, Equations (8.1) and
(8.7); local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 79--82,
149--153, and 1352--1358.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {D : ℕ}

private lemma frobenius_norm_sq_eq_sum_sqrt_eigenvalues_sq
    (A : Matrix (Fin D) (Fin D) ℂ) :
    ‖A‖ ^ 2 = ∑ i,
      Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) ^ 2 := by
  let hH : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  calc
    ‖A‖ ^ 2 = (Aᴴ * A).trace.re :=
      (trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq A).symm
    _ = ∑ i, hH.isHermitian.eigenvalues i := by
      rw [hH.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
      simp
    _ = ∑ i, Real.sqrt (hH.isHermitian.eigenvalues i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (Real.sq_sqrt (hH.eigenvalues_nonneg i)).symm

/-- The Hilbert--Schmidt norm is at most the trace norm.

This is the `p = 1`, `p' = 2` case of Wolf's Equation (8.1), reused at source line 1358 in
the proof of Equation (8.117). -/
theorem frobenius_norm_le_traceNorm (A : Matrix (Fin D) (Fin D) ℂ) :
    ‖A‖ ≤ traceNorm A := by
  let hH : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  let s : Fin D → ℝ := fun i ↦ Real.sqrt (hH.isHermitian.eigenvalues i)
  have hs_nonneg : ∀ i, 0 ≤ s i := fun i ↦ Real.sqrt_nonneg _
  have hsum_sq : ∑ i, s i ^ 2 = ‖A‖ ^ 2 := by
    simpa only [s, hH] using (frobenius_norm_sq_eq_sum_sqrt_eigenvalues_sq A).symm
  have hsq : ∑ i, s i ^ 2 ≤ (∑ i, s i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ hs_nonneg i
  have hsum_nonneg : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ ↦ hs_nonneg i
  rw [traceNorm_eq_sum_sqrt_eigenvalues]
  change ‖A‖ ≤ ∑ i, s i
  apply (sq_le_sq₀ (norm_nonneg A) hsum_nonneg).mp
  rw [← hsum_sq]
  exact hsq

/-- The trace norm is at most `√D` times the Hilbert--Schmidt norm.

This is the right inequality in Wolf's Equation (8.7), reused at source line 1352 in the proof of
Equation (8.115). -/
theorem traceNorm_le_sqrt_dim_mul_frobenius_norm (A : Matrix (Fin D) (Fin D) ℂ) :
    traceNorm A ≤ Real.sqrt D * ‖A‖ := by
  let hH : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  let s : Fin D → ℝ := fun i ↦ Real.sqrt (hH.isHermitian.eigenvalues i)
  have hs_nonneg : ∀ i, 0 ≤ s i := fun i ↦ Real.sqrt_nonneg _
  have hsum_sq : ∑ i, s i ^ 2 = ‖A‖ ^ 2 := by
    simpa only [s, hH] using (frobenius_norm_sq_eq_sum_sqrt_eigenvalues_sq A).symm
  have hcs : (∑ i, s i) ^ 2 ≤ D * ∑ i, s i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := s))
  have hsum_nonneg : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ ↦ hs_nonneg i
  have hsqrt_sq : Real.sqrt (D : ℝ) ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  rw [traceNorm_eq_sum_sqrt_eigenvalues]
  change (∑ i, s i) ≤ Real.sqrt (D : ℝ) * ‖A‖
  rw [hsum_sq] at hcs
  apply (sq_le_sq₀ hsum_nonneg
    (mul_nonneg (Real.sqrt_nonneg (D : ℝ)) (norm_nonneg A))).mp
  rw [mul_pow, hsqrt_sq]
  exact hcs

end Matrix
