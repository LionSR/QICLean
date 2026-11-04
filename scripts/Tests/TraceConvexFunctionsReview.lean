/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceConvexFunctions
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Independent source-boundary regression for Wolf's convex trace-functions corollary.
The two matrices are negative definite and noncommuting, with spectra in an interval
excluding zero. The scalar function remains arbitrary. -/

open Matrix
open scoped Matrix ComplexOrder

noncomputable section

namespace TraceConvexFunctionsReview

private def negativeDiagonal : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![-1, -2]

private def rationalRotation : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![3 / 5, 4 / 5; -4 / 5, 3 / 5], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, map_ofNat,
        Fin.sum_univ_two]⟩

private def rotatedNegative : Matrix (Fin 2) (Fin 2) ℂ :=
  (rationalRotation : Matrix (Fin 2) (Fin 2) ℂ) * negativeDiagonal *
    star (rationalRotation : Matrix (Fin 2) (Fin 2) ℂ)

private lemma negativeDiagonal_hermitian : negativeDiagonal.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [negativeDiagonal, Matrix.conjTranspose_apply]

private lemma negativeDiagonal_spectrum :
    spectrum ℝ negativeDiagonal ⊆ Set.Icc (-2 : ℝ) (-1) := by
  intro x hx
  have hx' : (x : ℂ) ∈ spectrum ℂ negativeDiagonal :=
    (spectrum.algebraMap_mem_iff ℂ).mpr hx
  rw [negativeDiagonal, spectrum_diagonal] at hx'
  obtain ⟨i, hi⟩ := hx'
  fin_cases i <;>
    have hr := congrArg Complex.re hi <;>
    norm_num at hr <;> subst x <;> norm_num

private lemma rotatedNegative_hermitian : rotatedNegative.IsHermitian := by
  exact isHermitian_mul_mul_conjTranspose _ negativeDiagonal_hermitian

private lemma rotatedNegative_spectrum :
    spectrum ℝ rotatedNegative ⊆ Set.Icc (-2 : ℝ) (-1) := by
  simpa only [rotatedNegative, Unitary.spectrum_star_right_conjugate] using
    negativeDiagonal_spectrum

-- This interval excludes zero; no default value of f at zero enters the theorem.
example : (0 : ℝ) ∉ Set.Icc (-2 : ℝ) (-1) := by norm_num

example : ¬ Commute negativeDiagonal rotatedNegative := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h.eq
  norm_num [negativeDiagonal, rotatedNegative, rationalRotation,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, map_ofNat,
    Fin.sum_univ_two] at h01

example : ¬ negativeDiagonal.PosSemidef := by
  intro h
  have h0 := h.re_dotProduct_nonneg (Pi.single 0 1)
  norm_num [negativeDiagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0

example : ¬ rotatedNegative.PosSemidef := by
  intro h
  have h0 := h.re_dotProduct_nonneg (Pi.single 0 1)
  norm_num [negativeDiagonal, rotatedNegative, rationalRotation,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.diagonal_apply,
    map_ofNat, Fin.sum_univ_two] at h0

-- Apply the actual public names to arbitrary scalar convex functions and all mixing parameters.
example {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Icc (-2 : ℝ) (-1)) f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t • negativeDiagonal + (1 - t) • rotatedNegative) ∈
        hermitianSpectralDomain (Fin 2) (Set.Icc (-2 : ℝ) (-1)) ∧
      (cfc f (t • negativeDiagonal + (1 - t) • rotatedNegative)).trace.re ≤
        t * (cfc f negativeDiagonal).trace.re +
          (1 - t) * (cfc f rotatedNegative).trace.re := by
  have ha : negativeDiagonal ∈ hermitianSpectralDomain (Fin 2)
      (Set.Icc (-2 : ℝ) (-1)) :=
    ⟨negativeDiagonal_hermitian, negativeDiagonal_spectrum⟩
  have hb : rotatedNegative ∈ hermitianSpectralDomain (Fin 2)
      (Set.Icc (-2 : ℝ) (-1)) :=
    ⟨rotatedNegative_hermitian, rotatedNegative_spectrum⟩
  exact ⟨convex_hermitianSpectralDomain hf.1 ha hb ht.1 (sub_nonneg.mpr ht.2)
      (by ring),
    by simpa only [ha.1.cfc_eq, hb.1.cfc_eq] using
      ha.1.trace_cfc_convex_le hf hb.1 ha.2 hb.2 ht.1 (sub_nonneg.mpr ht.2) (by ring)⟩

end TraceConvexFunctionsReview
