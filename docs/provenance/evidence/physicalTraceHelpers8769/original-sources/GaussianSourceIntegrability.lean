/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianCoefficients
import QICLean.Probability.WeightedSourceError

/-!
# Integrability of actual Gaussian source contractions

Pairwise second moments of the scalar coefficients imply integrability of the
trace norm of every finite matrix combination. Applying this to the original
source occurrences gives the integrability of each corrected partial branch,
also after any fixed physical projection or partial trace of its coefficient
matrices. No covariance value or operator norm bound is needed here.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 434–549.
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

end ProbabilityTheory

namespace TNLean.PEPS.PairEffect.SourceCircuit
open QICLean.ComplexGaussian

open Classical in
/-- Every matrix combination of the actual corrected-source coefficients has
integrable trace norm under the one global Gaussian law. -/
theorem integrable_rectangularTraceNorm_sourceCorrectionSum {P m n : Type}
    [Fintype m] [Fintype n] {a b : Layout P} (w : SourceCircuit a b)
    (k : ℕ) (hk : 0 < k) (S : Finset (sourceLocations w))
    (ξ ζ : ∀ e : S, branchLabels w e.1.1)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (M : ((∀ e : S, Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
      Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2)) ×
      (∀ e : S, Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
        Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2))) → Matrix m n ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (∑ q, (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) • M q)) (sourceGaussianLaw w k) := by
  apply ProbabilityTheory.integrable_rectangularTraceNorm_sum
  intro q r
  exact integrable_sourceCorrection_product_mul_conj w k hk S ξ ζ lam hnonneg
    q.1 r.1 q.2 r.2

end TNLean.PEPS.PairEffect.SourceCircuit
