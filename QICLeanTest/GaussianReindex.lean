/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.Reindex
import Mathlib.Tactic.NormNum

/-!
# Finite-reindex Gaussian consumers

The source indices are `Fin 2` and the target indices are `Bool`. Asymmetric
complex off-diagonal entries distinguish coordinate transport from transposition
and conjugation. Distinct non-Hermitian generators check that covariance needs
neither Hermiticity nor an exchange of generators. The tests also cover zero
variance, an empty truncation interval, and different empty index types.
-/

open Matrix Complex GaussianFilter MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace GaussianReindexTest

private def W : Matrix (Fin 2) (Fin 2) ℂ := !![1, I; 2 * I, 3]

private def H' : Matrix (Fin 2) (Fin 2) ℂ := !![I, 1; 0, 2]

private def H : Matrix (Fin 2) (Fin 2) ℂ := !![3, 0; I, -I]

-- Both generators genuinely fall outside the Hermitian contract of norm estimates.
example : ¬ H'.IsHermitian := by
  intro hH'
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).im) hH'.eq
  norm_num [H', Matrix.conjTranspose_apply, Complex.star_def] at h

example : ¬ H.IsHermitian := by
  intro hH
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).im) hH.eq
  norm_num [H, Matrix.conjTranspose_apply, Complex.star_def] at h

example : H' ≠ H := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).im) h
  norm_num [H', H] at h00

-- Reindexing keeps both complex phases and the original row/column order.
example : reindex finTwoEquiv finTwoEquiv W false true = I := rfl

example : reindex finTwoEquiv finTwoEquiv W true false = 2 * I := rfl

-- Exponentiation and its time path transport between the two different types.
example :
    NormedSpace.exp (reindex finTwoEquiv finTwoEquiv H') false true =
      NormedSpace.exp H' 0 1 := by
  rw [← reindex_exp]
  rfl

example (t : ℝ) :
    hermitianUnitaryPath (reindex finTwoEquiv finTwoEquiv H') t false true =
      hermitianUnitaryPath H' t 0 1 := by
  rw [← reindex_hermitianUnitaryPath]
  rfl

-- No measurability or integrability hypothesis is required for a general integral.
example (μ : Measure ℝ) (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) :
    (∫ t, reindex finTwoEquiv finTwoEquiv (f t) ∂μ) false true =
      (∫ t, f t ∂μ) 0 1 := by
  rw [← reindex_integral]
  rfl

-- In particular, the two exponential factors keep their generators and time signs.
example (t : ℝ) :
    (hermitianUnitaryPath (reindex finTwoEquiv finTwoEquiv H') t *
      reindex finTwoEquiv finTwoEquiv W *
      hermitianUnitaryPath (reindex finTwoEquiv finTwoEquiv H) (-t)) false true =
      (hermitianUnitaryPath H' t * W * hermitianUnitaryPath H (-t)) 0 1 := by
  rw [← reindex_intertwinerIntegrand]
  rfl

example (h : ℝ≥0) :
    gaussianIntertwiner h
      (reindex finTwoEquiv finTwoEquiv H')
      (reindex finTwoEquiv finTwoEquiv H)
      (reindex finTwoEquiv finTwoEquiv W) false true =
      gaussianIntertwiner h H' H W 0 1 := by
  rw [← reindex_gaussianIntertwiner]
  rfl

example (h : ℝ≥0) (T : ℝ) :
    gaussianIntertwinerTruncated h T
      (reindex finTwoEquiv finTwoEquiv H')
      (reindex finTwoEquiv finTwoEquiv H)
      (reindex finTwoEquiv finTwoEquiv W) true false =
      gaussianIntertwinerTruncated h T H' H W 1 0 := by
  rw [← reindex_gaussianIntertwinerTruncated]
  rfl

-- The Dirac-measure endpoint transports the actual non-real input entry.
example :
    reindex finTwoEquiv finTwoEquiv (gaussianIntertwiner 0 H' H W) false true = I := by
  rw [gaussianIntertwiner_zero_variance]
  rfl

example :
    gaussianIntertwiner 0
      (reindex finTwoEquiv finTwoEquiv H')
      (reindex finTwoEquiv finTwoEquiv H)
      (reindex finTwoEquiv finTwoEquiv W) true false = 2 * I := by
  rw [← reindex_gaussianIntertwiner, gaussianIntertwiner_zero_variance]
  rfl

-- A negative cutoff restricts to the empty set, with no renormalization.
example (h : ℝ≥0) :
    gaussianIntertwinerTruncated h (-1)
      (reindex finTwoEquiv finTwoEquiv H')
      (reindex finTwoEquiv finTwoEquiv H)
      (reindex finTwoEquiv finTwoEquiv W) = 0 := by
  simp [gaussianIntertwinerTruncated]

-- Empty source and target types are equivalent without a nonempty assumption.
example (h : ℝ≥0) (H' H W : Matrix (Fin 0) (Fin 0) ℂ) :
    reindex finZeroEquiv finZeroEquiv (gaussianIntertwiner h H' H W) =
      gaussianIntertwiner h (reindex finZeroEquiv finZeroEquiv H')
        (reindex finZeroEquiv finZeroEquiv H) (reindex finZeroEquiv finZeroEquiv W) :=
  reindex_gaussianIntertwiner finZeroEquiv h H' H W

example (h : ℝ≥0) (T : ℝ) (H' H W : Matrix (Fin 0) (Fin 0) ℂ) :
    reindex finZeroEquiv finZeroEquiv (gaussianIntertwinerTruncated h T H' H W) =
      gaussianIntertwinerTruncated h T (reindex finZeroEquiv finZeroEquiv H')
        (reindex finZeroEquiv finZeroEquiv H) (reindex finZeroEquiv finZeroEquiv W) :=
  reindex_gaussianIntertwinerTruncated finZeroEquiv h T H' H W

end GaussianReindexTest

/--
info: 'Matrix.reindex_exp' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.reindex_exp

/--
info: 'Matrix.reindex_hermitianUnitaryPath' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.reindex_hermitianUnitaryPath

/--
info: 'Matrix.reindex_integral' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.reindex_integral

/--
info: 'GaussianFilter.reindex_intertwinerIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.reindex_intertwinerIntegrand

/--
info: 'GaussianFilter.reindex_gaussianIntertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.reindex_gaussianIntertwiner

/--
info: 'GaussianFilter.reindex_gaussianIntertwinerTruncated' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.reindex_gaussianIntertwinerTruncated
