/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.WeylMonotonicity

/-!
# Unitary comparison for monotone scalar functions

This file proves the corrected form of the unitary comparison following Weyl's
monotonicity theorem in Wolf, Chapter 5.  If Hermitian matrices satisfy
`A ≤ B`, their decreasingly ordered eigenvalues satisfy
`λⱼ↓(A) ≤ λⱼ↓(B)`.  Aligning the corresponding ordered eigenbases therefore
gives one unitary `U` such that

`f(A) ≤ U * f(B) * U†`

for every scalar function `f` that is nondecreasing on an interval containing
both spectra.  The same `U` works for all such intervals and functions.

The order hypothesis is indispensable: it is present in Wolf's immediately
preceding statement of Weyl monotonicity, but absent from the original printed
statement of the proposition containing Equation (5.57).

## Main result

* `Matrix.IsHermitian.exists_unitary_cfc_le_cfc_of_le` is the corrected form of
  Wolf's unitary comparison, Equation (5.57).

## Reference

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Equations (5.56)--(5.57)][Wolf2012QChannels]
-/

open scoped ComplexOrder MatrixOrder

namespace Matrix.IsHermitian

/-- **Wolf's unitary comparison for monotone scalar functions (corrected).**
Let `A` and `B` be Hermitian matrices with `A ≤ B`.  There is a unitary `U`,
depending only on their decreasingly ordered eigenbases, such that
`f(A) ≤ U * f(B) * U†` whenever `f` is nondecreasing on an interval containing
both spectra.

No continuity assumption on `f` is needed: the spectrum of a finite matrix is
finite, so every function on it is continuous. -/
theorem exists_unitary_cfc_le_cfc_of_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A ≤ B) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      ∀ (I : Set ℝ) (f : ℝ → ℝ), I.OrdConnected →
        spectrum ℝ A ⊆ I → spectrum ℝ B ⊆ I → MonotoneOn f I →
        cfc f A ≤ (U : Matrix n n ℂ) * cfc f B * star (U : Matrix n n ℂ) := by
  let UA : Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary
  let UB : Matrix.unitaryGroup n ℂ := hB.eigenvectorUnitary
  refine ⟨UA * star UB, ?_⟩
  intro I f _hI hspecA hspecB hf
  let DA : Matrix n n ℂ :=
    Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))
  let DB : Matrix n n ℂ :=
    Matrix.diagonal (fun i => (f (hB.eigenvalues i) : ℂ))
  have hf_eigenvalues (i : n) : f (hA.eigenvalues i) ≤ f (hB.eigenvalues i) :=
    hf (hspecA (hA.eigenvalues_mem_spectrum_real i))
      (hspecB (hB.eigenvalues_mem_spectrum_real i))
      (hA.eigenvalues_mono hB hAB i)
  have hDBDA : (DB - DA).PosSemidef := by
    rw [show DB - DA = Matrix.diagonal
      (fun i => ((f (hB.eigenvalues i) - f (hA.eigenvalues i) : ℝ) : ℂ)) from by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [DA, DB]
        · simp [DA, DB, hij]]
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    simpa using sub_nonneg.mpr (hf_eigenvalues i)
  have hconj :
      ((UA : Matrix n n ℂ) * (DB - DA) * star (UA : Matrix n n ℂ)).PosSemidef := by
    simpa only [star_eq_conjTranspose] using
      hDBDA.mul_mul_conjTranspose_same (UA : Matrix n n ℂ)
  have haligned :
      (UA : Matrix n n ℂ) * DA * star (UA : Matrix n n ℂ) ≤
        (UA : Matrix n n ℂ) * DB * star (UA : Matrix n n ℂ) := by
    rw [Matrix.le_iff]
    simpa only [mul_sub, sub_mul] using hconj
  have hAcfc :
      cfc f A = (UA : Matrix n n ℂ) * DA * star (UA : Matrix n n ℂ) := by
    rw [hA.cfc_eq]
    rfl
  have hBcfc :
      cfc f B = (UB : Matrix n n ℂ) * DB * star (UB : Matrix n n ℂ) := by
    rw [hB.cfc_eq]
    rfl
  rw [hAcfc, hBcfc]
  apply haligned.trans_eq
  rw [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star]
  change (UA : Matrix n n ℂ) * DB * star (UA : Matrix n n ℂ) =
    (((UA : Matrix n n ℂ) * star (UB : Matrix n n ℂ)) *
      ((UB : Matrix n n ℂ) * DB * star (UB : Matrix n n ℂ))) *
      ((UB : Matrix n n ℂ) * star (UA : Matrix n n ℂ))
  have hUB : star (UB : Matrix n n ℂ) * (UB : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self UB
  calc
    (UA : Matrix n n ℂ) * DB * star (UA : Matrix n n ℂ) =
        (UA : Matrix n n ℂ) *
          (star (UB : Matrix n n ℂ) * (UB : Matrix n n ℂ)) * DB *
          (star (UB : Matrix n n ℂ) * (UB : Matrix n n ℂ)) *
          star (UA : Matrix n n ℂ) := by rw [hUB]; simp
    _ = (((UA : Matrix n n ℂ) * star (UB : Matrix n n ℂ)) *
          ((UB : Matrix n n ℂ) * DB * star (UB : Matrix n n ℂ))) *
          ((UB : Matrix n n ℂ) * star (UA : Matrix n n ℂ)) := by
      noncomm_ring

end Matrix.IsHermitian
