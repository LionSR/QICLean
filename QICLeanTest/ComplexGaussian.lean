/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.Covariance

/-! Circular complex Gaussian covariance regressions with coincident indices,
zero weights, unequal supports and empty sample families. -/
open MeasureTheory ProbabilityTheory QICLean.ComplexGaussian
open scoped ComplexConjugate

-- All four coordinates coincide: the centered variance is 1.
example : (∫ x, centered (0 : Fin 2) 0 x * conj (centered (0 : Fin 2) 0 x)
    ∂law (Fin 2)) = 1 := by
  simpa [delta] using integral_centered_mul_conj (0 : Fin 2) 0 0 0

-- Two diagonal coefficients at different coordinates have zero centered covariance.
example : (∫ x, centered (0 : Fin 2) 0 x * conj (centered (1 : Fin 2) 1 x)
    ∂law (Fin 2)) = 0 := by
  simpa [delta] using integral_centered_mul_conj (0 : Fin 2) 0 1 1

-- The offdiagonal coefficient still has unit variance.
example : (∫ x, centered (0 : Fin 2) 1 x * conj (centered (0 : Fin 2) 1 x)
    ∂law (Fin 2)) = 1 := by
  simpa [delta] using integral_centered_mul_conj (0 : Fin 2) 1 0 1

-- Averaging two samples halves the variance.
example : (∫ x, sampleAverage 2 (0 : Fin 2) 1 x *
    conj (sampleAverage 2 (0 : Fin 2) 1 x) ∂law (Fin 2 × Fin 2)) = (1 / 2 : ℂ) := by
  simpa [delta] using integral_sampleAverage_mul_conj 2 (by decide) (0 : Fin 2) 1 0 1

-- Unit-variance complex normalization gives fourth moment 2.
example : (∫ x, ‖coordinate (0 : Fin 1) x‖ ^ 4 ∂law (Fin 1)) = 2 :=
  integral_coordinate_norm_four 0

-- Empty sample sums remain defined; the positive-k covariance theorem is separate.
example (a b : Fin 2) (x : Sample (Fin 0 × Fin 2)) : sampleAverage 0 a b x = 0 := by
  simp [sampleAverage]

-- Ket and bra dimensions can differ, and zero weights need no support inversion.
example (x : Sample (Fin 2 × (Fin 2 × Fin 3))) :
    densityCoefficient 2 (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ))
      ((0, 1), (2, 0)) x = 0 := by
  norm_num [densityCoefficient, coefficientWeight]

-- Empty coordinate families still have a genuine probability law.
example : IsProbabilityMeasure (law (Fin 0)) := inferInstance
