/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Probability.WeightedSourceError

/-!
# Integrability of finite matrix trace-norm sums

For a finite measure, pairwise integrable products of scalar coefficients give
an integrable trace norm for each finite fixed matrix combination. In particular,
square-integrability of every coefficient suffices. Independence and covariance
values are not required.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 434–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-second-moment.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: p09-qic-matrixtracenormintegrability-01
Downstream declaration:
ProbabilityTheory.integrable_rectangularTraceNorm_sum

Provenance-ID: p09-qic-matrixtracenormintegrability-02
Downstream declaration:
ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two

-/

noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate

namespace ProbabilityTheory

/-- Pairwise integrable coefficient products give an integrable trace norm for
every finite matrix combination over a finite measure. -/
theorem integrable_rectangularTraceNorm_sum {Ω J m n : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Fintype J] [Fintype m] [Fintype n] [DecidableEq n]
    (z : J → Ω → ℂ)
    (hz : ∀ i j, Integrable (fun ω ↦ z i ω * conj (z j ω)) μ)
    (A : J → Matrix m n ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm (∑ i, z i ω • A i)) μ := by
  have hn (i : J) : Integrable (fun ω ↦ ‖z i ω‖) μ := by
    have hs : Integrable (fun ω ↦ ‖z i ω‖ ^ 2) μ := by
      simpa only [norm_mul, Complex.norm_conj, ← pow_two] using (hz i i).norm
    have hm : AEStronglyMeasurable (fun ω ↦ ‖z i ω‖) μ := by
      have h := Real.continuous_sqrt.comp_aestronglyMeasurable hs.aestronglyMeasurable
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm] using h
    exact ((memLp_two_iff_integrable_sq hm).mpr hs).integrable (by norm_num)
  have hu := integrable_finsetSum Finset.univ fun i _ ↦
    (hn i).mul_const (Matrix.rectangularTraceNorm (A i))
  refine hu.mono' (aestronglyMeasurable_rectangularTraceNorm_sum z hz A) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Matrix.rectangularTraceNorm_nonneg _)]
  exact Matrix.rectangularTraceNorm_sum_smul_le _ _ _

/-- Square-integrable coefficients give an integrable trace norm for every
finite fixed matrix combination. No independence between coefficients is needed. -/
theorem integrable_rectangularTraceNorm_sum_of_memLp_two {Ω J m n : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Fintype J] [Fintype m] [Fintype n] [DecidableEq n]
    (z : J → Ω → ℂ) (hz : ∀ i, MemLp (z i) 2 μ) (M : J → Matrix m n ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm (∑ i, z i ω • M i)) μ := by
  apply integrable_rectangularTraceNorm_sum z _ M
  intro i j
  have hj : MemLp (fun ω ↦ conj (z j ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm
      (Complex.continuous_conj.comp_aestronglyMeasurable (hz j).aestronglyMeasurable)).mpr
    simpa only [Complex.norm_conj] using
      (memLp_two_iff_integrable_sq_norm (hz j).aestronglyMeasurable).mp (hz j)
  exact (hz i).integrable_mul hj

end ProbabilityTheory
