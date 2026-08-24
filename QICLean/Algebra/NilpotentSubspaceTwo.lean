/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Complex.Basic

/-!
# Nilpotent subspaces of 2×2 complex matrices

A **nilpotent subspace** of `M₂(ℂ)` is a linear subspace all of whose elements
are nilpotent.  This file proves the two-dimensional classification: every
nilpotent subspace of `2 × 2` complex matrices has a common kernel vector, and
equivalently has dimension at most one.

This is the `D = 2` case of the classification used for the low-dimensional
quantum Wielandt corollary (Sanz–Pérez-García–Wolf–Cirac, arXiv:0909.5347,
remark after Theorem 1; Wolf, *Quantum Channels & Operations*, Chapter 6,
corollary after Theorem 6.9, `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`
lines 1111–1127), where the classification is attributed to
M. A. Fasoli, *Classification of nilpotent linear spaces in M(4; ℂ)*,
Communications in Algebra 25(6):1919–1932, 1997.

## Main results

* `exists_smul_of_isNilpotent_add_fin_two`: two nilpotent `2 × 2` complex
  matrices whose sum is again nilpotent are proportional.
* `exists_common_ker_of_isNilpotent_submodule_fin_two`: a nilpotent subspace
  of `M₂(ℂ)` has a common kernel vector.
* `finrank_le_one_of_isNilpotent_submodule_fin_two`: a nilpotent subspace of
  `M₂(ℂ)` has dimension at most one.
-/

open scoped Matrix

namespace QICLean

/-- A nilpotent complex matrix has zero determinant. -/
theorem IsNilpotent.det_eq_zero_of_complex {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {M : Matrix n n ℂ} (hM : IsNilpotent M) : M.det = 0 := by
  obtain ⟨k, hk⟩ := hM
  have h : IsNilpotent M.det := ⟨k, by rw [← Matrix.det_pow, hk, Matrix.det_zero]⟩
  exact IsNilpotent.eq_zero h

/-- A nilpotent complex matrix has zero trace. -/
theorem IsNilpotent.trace_eq_zero_of_complex {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : IsNilpotent M) : M.trace = 0 :=
  IsNilpotent.eq_zero (Matrix.isNilpotent_trace_of_isNilpotent hM)

/-- Two nilpotent `2 × 2` complex matrices whose sum is again nilpotent are
proportional: one is a scalar multiple of the other.

Writing `M = (a, b; c, -a)` and `N = (α, β; γ, -α)` (both traces vanish), the
hypotheses give `a² + bc = 0`, `α² + βγ = 0`, and the mixed condition
`2aα + bγ + βc = 0` from `det (M + N) = 0`; together these force the two
matrices to be linearly dependent. -/
theorem exists_smul_of_isNilpotent_add_fin_two {M N : Matrix (Fin 2) (Fin 2) ℂ}
    (hN : N ≠ 0) (hM : IsNilpotent M) (hN' : IsNilpotent N)
    (hMN : IsNilpotent (M + N)) :
    ∃ c : ℂ, M = c • N := by
  have htrM : M.trace = 0 := IsNilpotent.trace_eq_zero_of_complex hM
  have htrN : N.trace = 0 := IsNilpotent.trace_eq_zero_of_complex hN'
  have hdetM : M.det = 0 := IsNilpotent.det_eq_zero_of_complex hM
  have hdetN : N.det = 0 := IsNilpotent.det_eq_zero_of_complex hN'
  have hdetMN : (M + N).det = 0 := IsNilpotent.det_eq_zero_of_complex hMN
  rw [Matrix.trace_fin_two] at htrM htrN
  rw [Matrix.det_fin_two] at hdetM hdetN hdetMN
  simp only [Matrix.add_apply] at hdetMN
  have hM11 : M 1 1 = -M 0 0 := by linear_combination htrM
  have hN11 : N 1 1 = -N 0 0 := by linear_combination htrN
  rw [hM11] at hdetM
  rw [hN11] at hdetN
  rw [hM11, hN11] at hdetMN
  have hMa : M 0 0 ^ 2 + M 0 1 * M 1 0 = 0 := by linear_combination -hdetM
  have hNa : N 0 0 ^ 2 + N 0 1 * N 1 0 = 0 := by linear_combination -hdetN
  have hmix : 2 * M 0 0 * N 0 0 + M 0 1 * N 1 0 + N 0 1 * M 1 0 = 0 := by
    linear_combination -hdetMN + hdetM + hdetN
  by_cases hβ : N 0 1 = 0
  · -- If `N 0 1 = 0`, then `N 0 0 = 0`, so `N = γ • E₁₀` with `γ ≠ 0`; the
    -- mixed condition gives `M 0 1 = 0`, hence `M 0 0 = 0` and `M = c • E₁₀`.
    have hα0 : N 0 0 = 0 := by
      rw [hβ] at hNa
      simp only [zero_mul, add_zero] at hNa
      exact sq_eq_zero_iff.mp hNa
    have hγ : N 1 0 ≠ 0 := by
      intro hγ0
      apply hN
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hN11, hα0, hβ, hγ0]
    have hb0 : M 0 1 = 0 := by
      rw [hα0, hβ] at hmix
      simp only [mul_zero, zero_mul, add_zero, zero_add] at hmix
      exact (mul_eq_zero.mp hmix).resolve_right hγ
    have ha0 : M 0 0 = 0 := by
      rw [hb0] at hMa
      simp only [zero_mul, add_zero] at hMa
      exact sq_eq_zero_iff.mp hMa
    refine ⟨M 1 0 * (N 1 0)⁻¹, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM11, hN11, ha0, hb0, hα0, hβ, hγ]
  · -- If `N 0 1 ≠ 0`, the key identity is `(M 0 1)(N 0 0) = (M 0 0)(N 0 1)`.
    have h1 : 2 * M 0 0 * N 0 0 * N 0 1 - M 0 1 * N 0 0 ^ 2
        + N 0 1 ^ 2 * M 1 0 = 0 := by
      linear_combination hmix * N 0 1 - hNa * M 0 1
    have hkey : M 0 1 * N 0 0 = M 0 0 * N 0 1 := by
      have hsq : (M 0 1 * N 0 0 - M 0 0 * N 0 1) ^ 2 = 0 := by
        linear_combination hMa * N 0 1 ^ 2 - h1 * M 0 1
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    refine ⟨M 0 1 * (N 0 1)⁻¹, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one]
    · field_simp
      linear_combination -hkey
    · field_simp
    · have h2 : N 0 1 * (N 0 1 * M 1 0 - M 0 1 * N 1 0) = 0 := by
        linear_combination hmix * N 0 1 + 2 * N 0 0 * hkey - 2 * M 0 1 * hNa
      have h3 : N 0 1 * M 1 0 - M 0 1 * N 1 0 = 0 :=
        (mul_eq_zero.mp h2).resolve_left hβ
      field_simp
      linear_combination h3
    · rw [hM11, hN11]
      field_simp
      linear_combination hkey

/-- A nilpotent `2 × 2` complex matrix has a nonzero kernel vector. -/
theorem exists_ker_vec_of_isNilpotent_fin_two {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : IsNilpotent M) : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mpr (IsNilpotent.det_eq_zero_of_complex hM)

/-- **Classification of nilpotent subspaces of `M₂(ℂ)`**: every linear
subspace of `2 × 2` complex matrices all of whose elements are nilpotent has a
common kernel vector.

Wolf, *Quantum Channels & Operations*, Chapter 6, corollary after Theorem 6.9
(`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1114--1127):
"for `d = 2` its dimension would have to be one". -/
theorem exists_common_ker_of_isNilpotent_submodule_fin_two
    (S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (hS : ∀ M ∈ S, IsNilpotent M) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ ∀ M ∈ S, M *ᵥ v = 0 := by
  rcases eq_or_ne S ⊥ with rfl | hbot
  · refine ⟨![1, 0], ?_, fun M hM => ?_⟩
    · intro h
      have := congr_fun h 0
      simp at this
    · rw [Submodule.mem_bot] at hM
      subst hM
      simp
  · obtain ⟨N, hNS, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨v, hv, hNv⟩ := exists_ker_vec_of_isNilpotent_fin_two (hS N hNS)
    refine ⟨v, hv, fun M hM => ?_⟩
    obtain ⟨c, rfl⟩ := exists_smul_of_isNilpotent_add_fin_two hN0 (hS M hM)
      (hS N hNS) (hS (M + N) (S.add_mem hM hNS))
    simp [Matrix.smul_mulVec, hNv]

/-- **Dimension form of the classification**: a nilpotent subspace of `M₂(ℂ)`
has dimension at most one. -/
theorem finrank_le_one_of_isNilpotent_submodule_fin_two
    (S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (hS : ∀ M ∈ S, IsNilpotent M) :
    Module.finrank ℂ S ≤ 1 := by
  rcases eq_or_ne S ⊥ with rfl | hbot
  · simp
  · obtain ⟨N, hNS, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hle : S ≤ ℂ ∙ N := by
      intro M hM
      obtain ⟨c, hc⟩ := exists_smul_of_isNilpotent_add_fin_two hN0 (hS M hM)
        (hS N hNS) (hS (M + N) (S.add_mem hM hNS))
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    calc Module.finrank ℂ S
        ≤ Module.finrank ℂ (ℂ ∙ N : Submodule ℂ _) :=
          Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton hN0

end QICLean
