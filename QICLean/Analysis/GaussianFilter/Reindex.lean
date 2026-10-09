/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.MatrixIntegral
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Gaussian filters under finite reindexing

Simultaneous reindexing of rows and columns commutes with the actual full and
unrenormalized truncated Gaussian integrals. The proof uses Mathlib's existing
matrix algebra and linear equivalences: the algebra equivalence preserves the
exponential, and its continuous linear equivalence commutes with the Bochner
integral. No new coordinate map, convergence hypothesis, or integral-output
hypothesis is introduced.

The statements include zero variance, every real cutoff, and empty finite index
types. The input matrix and generators can be arbitrary complex matrices; in
particular, reindexing neither conjugates entries nor exchanges the generators.
This is the generic coordinate-transport step for the Gaussian-filter passage
of `peps-02-information-adc7f124.tex`, lines 426–452. Regional tensor-network
coordinate identifications are separate downstream results.
-/

open MeasureTheory Matrix ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The matrix exponential is natural under a simultaneous finite reindexing. -/
theorem reindex_exp (e : n ≃ m) (A : Matrix n n ℂ) :
    reindex e e (NormedSpace.exp A) = NormedSpace.exp (reindex e e A) := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (reindexAlgEquiv ℂ ℂ e)
    (reindexLinearEquiv ℂ ℂ e e).toContinuousLinearEquiv.continuous A

/-- Reindexing preserves the generator and time of the exponential path. -/
theorem reindex_hermitianUnitaryPath (e : n ≃ m) (H : Matrix n n ℂ) (t : ℝ) :
    reindex e e (hermitianUnitaryPath H t) =
      hermitianUnitaryPath (reindex e e H) t := by
  unfold hermitianUnitaryPath
  rw [reindex_exp]
  rfl

/-- Reindexing commutes with the Bochner integral, including its nonintegrable
convention, because reindexing is a continuous linear equivalence. -/
theorem reindex_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e : n ≃ m) (f : α → Matrix n n ℂ) :
    reindex e e (∫ x, f x ∂μ) = ∫ x, reindex e e (f x) ∂μ := by
  exact ((reindexLinearEquiv ℂ ℂ e e).toContinuousLinearEquiv.integral_comp_comm f).symm

end Matrix

namespace GaussianFilter

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Both generators and the middle matrix are transported in their original order. -/
theorem reindex_intertwinerIntegrand (e : n ≃ m) (H' H W : Matrix n n ℂ) (t : ℝ) :
    reindex e e (hermitianUnitaryPath H' t * W * hermitianUnitaryPath H (-t)) =
      hermitianUnitaryPath (reindex e e H') t * reindex e e W *
        hermitianUnitaryPath (reindex e e H) (-t) := by
  change (reindexAlgEquiv ℂ ℂ e)
    (hermitianUnitaryPath H' t * W * hermitianUnitaryPath H (-t)) = _
  rw [map_mul, map_mul]
  simp only [coe_reindexAlgEquiv, reindex_hermitianUnitaryPath]

/-- Finite coordinate changes commute with the actual full Gaussian filter. -/
theorem reindex_gaussianIntertwiner (e : n ≃ m) (h : ℝ≥0)
    (H' H W : Matrix n n ℂ) :
    reindex e e (gaussianIntertwiner h H' H W) =
      gaussianIntertwiner h (reindex e e H') (reindex e e H) (reindex e e W) := by
  unfold gaussianIntertwiner
  rw [reindex_integral]
  simp_rw [reindex_intertwinerIntegrand]

/-- Finite coordinate changes commute with the actual truncated Gaussian filter.
The restricted measure, cutoff, and original Gaussian mass are unchanged. -/
theorem reindex_gaussianIntertwinerTruncated (e : n ≃ m) (h : ℝ≥0) (T : ℝ)
    (H' H W : Matrix n n ℂ) :
    reindex e e (gaussianIntertwinerTruncated h T H' H W) =
      gaussianIntertwinerTruncated h T
        (reindex e e H') (reindex e e H) (reindex e e W) := by
  unfold gaussianIntertwinerTruncated
  rw [reindex_integral]
  simp_rw [reindex_intertwinerIntegrand]

end GaussianFilter
