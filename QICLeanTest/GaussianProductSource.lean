/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.ProductSource

/-! Edge-case regressions for GaussianProductSource in the compression proof. -/

open MeasureTheory QICLean.ComplexGaussian
open scoped ComplexConjugate Matrix.Norms.Elementwise Kronecker

-- The rectangular operators have different ket and bra dimensions and share coordinates.
example (x : Sample (Fin 2 × (Fin 2 × Fin 3))) (j : Fin 2) (a : Fin 2) (c : Fin 3) :
    sourceV 2 (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ)) j x a c =
      conj (sourceU 2 (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ)) j x a c) := by
  simp [sourceU, sourceV, Matrix.of_apply]

-- A diagonal coordinate of the exact ket/bra outer product is nonzero.
example : schmidtSource (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ))
    (0, 0) (2, 2) = 1 := by
  simp [schmidtSource_apply]

-- An offdiagonal Schmidt row vanishes in the target and in expectation.
example : (∫ x, sampledSource 2 (fun _ : Fin 2 ↦ (1 : ℝ))
    (fun _ : Fin 3 ↦ (1 : ℝ)) x (0, 1) (2, 2)
      ∂law (Fin 2 × (Fin 2 × Fin 3))) = 0 := by
  rw [integral_sampledSource_entry 2 (by decide) _ _ (by simp) (by simp)]
  simp [schmidtSource_apply]

-- Coincident matrix entries have variance 1/k, with all Gaussian indices coincident.
example : (∫ x, sourceCorrection 2 (fun _ : Fin 2 ↦ (1 : ℝ))
    (fun _ : Fin 3 ↦ (1 : ℝ)) x (0, 0) (2, 2) *
      conj (sourceCorrection 2 (fun _ : Fin 2 ↦ (1 : ℝ))
        (fun _ : Fin 3 ↦ (1 : ℝ)) x (0, 0) (2, 2))
      ∂law (Fin 2 × (Fin 2 × Fin 3))) = (1 / 2 : ℂ) := by
  simpa using integral_sourceCorrection_entry_mul_conj 2 (by decide)
    (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ))
    (by simp) (by simp) (0, 0) (0, 0) (2, 2) (2, 2)

-- Distinct source entries have zero covariance, even when one Gaussian index is shared.
example : (∫ x, sourceCorrection 2 (fun _ : Fin 2 ↦ (1 : ℝ))
    (fun _ : Fin 3 ↦ (1 : ℝ)) x (0, 1) (2, 0) *
      conj (sourceCorrection 2 (fun _ : Fin 2 ↦ (1 : ℝ))
        (fun _ : Fin 3 ↦ (1 : ℝ)) x (0, 1) (2, 1))
      ∂law (Fin 2 × (Fin 2 × Fin 3))) = 0 := by
  simpa using integral_sourceCorrection_entry_mul_conj 2 (by decide)
    (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ))
    (by simp) (by simp) (0, 1) (0, 1) (2, 0) (2, 1)

-- Zero weights vanish without any support inverse or strictly positive weight premise.
example (x : Sample (Fin 2 × (Fin 2 × Fin 3))) :
    sourceCorrection 2 (fun _ : Fin 2 ↦ (0 : ℝ))
      (fun _ : Fin 3 ↦ (1 : ℝ)) x (0, 1) (2, 0) = 0 := by
  rw [sourceCorrection_apply 2 (by decide) _ _ (by simp) (by simp)]
  norm_num [densityCoefficient, coefficientWeight]

-- The average is a matrix-valued Bochner integral, not merely entrywise notation.
example : (∫ x, sampledSource 2 (fun _ : Fin 2 ↦ (1 : ℝ))
    (fun _ : Fin 3 ↦ (1 : ℝ)) x ∂law (Fin 2 × (Fin 2 × Fin 3))) =
      schmidtSource (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ)) :=
  integral_sampledSource 2 (by decide) _ _ (by simp) (by simp)

-- Empty Schmidt supports require no nonempty hypothesis.
example (mu : Fin 3 → ℝ) (hmu : ∀ c, 0 ≤ mu c) :
    (∫ x, sampledSource 1 (fun _ : Fin 0 ↦ (0 : ℝ)) mu x
      ∂law (Fin 1 × (Fin 0 × Fin 3))) =
        schmidtSource (fun _ : Fin 0 ↦ (0 : ℝ)) mu :=
  integral_sampledSource 1 (by decide) _ _ (by simp) hmu

-- Zero samples are defined, but unbiasedness correctly requires k > 0.
example (x : Sample (Fin 0 × (Fin 2 × Fin 3))) :
    sampledSource 0 (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ)) x = 0 := by
  simp [sampledSource]
