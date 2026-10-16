/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterOptimizer
import QICLean.Analysis.TraceCFC

/-!
# Trace normalization of feasible filters

For every positive weight `a`, the floor-zero feasible matrices are exactly the
positive-semidefinite matrices with `Tr (cfc (fun x ↦ x ^ (2 / a)) K) = 1`.
This includes singular matrices and empty finite index types. Reindexing preserves
feasibility at every floor and weight, without a sign assumption.

This is an equality of sets of matrices. It neither identifies nonunique spectral
coordinates nor compares ordered products, maximizing families, or unimported
source declarations. The powers below are real continuous-functional-calculus
powers; no identity with `Entropy.specPow` on singular matrices is asserted.

## Source and adaptation

The source filter convention is `PositiveFilter` and `tracePower` in
`openai/math`, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean`, lines 151–159.
The positivity and spectral reconstruction arguments are adapted from
`coordinateMatrix_positive` and `coordinateMatrix_surjective` in
`lean/OAI/MathematicalPhysics/PEPSFilters/Coordinates.lean`, lines 56–62
and 114–132 at that commit (Apache-2.0).
Changes: arbitrary finite matrix indices replace regional configurations;
`IsFeasibleFilter` replaces bundled unitary/simplex coordinates; the existing
QIC trace-of-conjugated-diagonal theorem proves normalization, without the source's
eigenvalue-permutation argument. The reindexing proof transports witnesses directly.
-/

open Complex Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Entropy

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A feasible filter at a nonnegative floor is positive semidefinite, for every
real weight. Adapted from source `Coordinates.lean`, lines 56–62. -/
theorem IsFeasibleFilter.posSemidef {f a : ℝ} {K : Matrix m m ℂ}
    (hK : IsFeasibleFilter f a K) (hf : 0 ≤ f) : K.PosSemidef := by
  obtain ⟨U, y, -, hy, -, rfl⟩ := hK
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact_mod_cast Real.rpow_nonneg (hf.trans (hy i)) (a / 2)

/-- The reciprocal real power of a floor-zero feasible filter has trace one.
The positive weight allows zero simplex entries and hence singular filters. -/
theorem IsFeasibleFilter.trace_cfc_rpow {a : ℝ} {K : Matrix m m ℂ}
    (hK : IsFeasibleFilter 0 a K) (ha : 0 < a) :
    (cfc (fun x : ℝ ↦ x ^ (2 / a)) K).trace = 1 := by
  obtain ⟨U, y, hU, hy, hs, rfl⟩ := hK
  rw [trace_cfc_conj_diagonal hU]
  have hp : ∀ i, (y i ^ (a / 2)) ^ (2 / a) = y i := by
    intro i
    rw [← Real.rpow_mul (hy i), show a / 2 * (2 / a) = 1 by field_simp [ha.ne'],
      Real.rpow_one]
  simp_rw [hp]
  rw [← Complex.ofReal_sum, hs, Complex.ofReal_one]

/-- For a positive weight, floor-zero feasibility is precisely positive
semidefiniteness and reciprocal trace-power normalization. The finite index type
may be empty. The converse adapts source `Coordinates.lean`, lines 114–132. -/
theorem isFeasibleFilter_zero_iff {a : ℝ} (ha : 0 < a) {K : Matrix m m ℂ} :
    IsFeasibleFilter 0 a K ↔
      K.PosSemidef ∧ (cfc (fun x : ℝ ↦ x ^ (2 / a)) K).trace = 1 := by
  constructor
  · intro hK
    exact ⟨hK.posSemidef le_rfl, hK.trace_cfc_rpow ha⟩
  · rintro ⟨hK, htr⟩
    refine ⟨hK.isHermitian.eigenvectorUnitary,
      fun i ↦ hK.isHermitian.eigenvalues i ^ (2 / a), ?_, ?_, ?_, ?_⟩
    · simpa only [star_eq_conjTranspose] using
        Unitary.coe_star_mul_self hK.isHermitian.eigenvectorUnitary
    · intro i
      exact Real.rpow_nonneg (hK.eigenvalues_nonneg i) _
    · rw [hK.isHermitian.cfc_eq, hK.isHermitian.trace_cfc_eq_sum,
        ← Complex.ofReal_sum] at htr
      exact_mod_cast htr
    · have hp (i : m) : (hK.isHermitian.eigenvalues i ^ (2 / a)) ^ (a / 2) =
          hK.isHermitian.eigenvalues i := by
        rw [← Real.rpow_mul (hK.eigenvalues_nonneg i),
          show 2 / a * (a / 2) = 1 by field_simp [ha.ne'], Real.rpow_one]
      simpa only [hp, star_eq_conjTranspose] using hK.isHermitian.spectral_form

/-- Source-shaped normalization for a positive-semidefinite filter, expressed as
the sum of reciprocal powers of its nonnegative eigenvalues. This is the matrix
condition in source `Basic.lean`, lines 155–159, without importing its filter type. -/
theorem isFeasibleFilter_zero_iff_eigenvalues {a : ℝ} (ha : 0 < a)
    {K : Matrix m m ℂ} (hK : K.PosSemidef) :
    IsFeasibleFilter 0 a K ↔ ∑ i, hK.isHermitian.eigenvalues i ^ (2 / a) = 1 := by
  rw [isFeasibleFilter_zero_iff ha, and_iff_right hK, hK.isHermitian.cfc_eq,
    hK.isHermitian.trace_cfc_eq_sum, ← Complex.ofReal_sum]
  rw [← Complex.ofReal_one, Complex.ofReal_inj]

/-- Reindexing the matrix and its simplex witness preserves feasibility for
arbitrary real floors and weights. -/
theorem IsFeasibleFilter.reindex {f a : ℝ} {K : Matrix m m ℂ}
    (hK : IsFeasibleFilter f a K) (e : m ≃ n) :
    IsFeasibleFilter f a (Matrix.reindex e e K) := by
  obtain ⟨U, y, hU, hy, hs, rfl⟩ := hK
  refine ⟨U.submatrix e.symm e.symm, y ∘ e.symm, ?_, fun i ↦ hy (e.symm i), ?_, ?_⟩
  · rw [conjTranspose_submatrix,
      submatrix_mul_equiv Uᴴ U e.symm e.symm e.symm, hU, submatrix_one_equiv]
  · exact (Equiv.sum_comp e.symm y).trans hs
  · change (U * diagonal (fun i ↦ ((y i ^ (a / 2) : ℝ) : ℂ)) * Uᴴ).submatrix
        e.symm e.symm = _
    rw [← submatrix_mul_equiv _ _ e.symm e.symm e.symm,
      ← submatrix_mul_equiv _ _ e.symm e.symm e.symm,
      submatrix_diagonal_equiv, conjTranspose_submatrix]

/-- Feasibility depends only on the matrix up to an equivalence of its finite
index set. No positivity or nonemptiness assumption is needed. -/
theorem isFeasibleFilter_reindex_iff (e : m ≃ n) {f a : ℝ} {K : Matrix m m ℂ} :
    IsFeasibleFilter f a (Matrix.reindex e e K) ↔ IsFeasibleFilter f a K := by
  constructor
  · intro hK
    simpa [Matrix.reindex_apply] using hK.reindex e.symm
  · exact fun hK ↦ hK.reindex e

end Entropy
