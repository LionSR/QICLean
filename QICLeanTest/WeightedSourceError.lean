/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.WeightedSourceError

/-! Edge-case regressions for WeightedSourceError in the compression proof. -/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]

-- Different full ket/bra dimensions and zero-support probability entries.
example (O : Matrix (Fin 3 × Fin 1) (Fin 2 × Fin 2) ℂ) (hO : ‖O‖ ≤ 1) :
    ∑ b : Fin 2 × Fin 3, Real.sqrt (![1, 0] b.1 * ![0, 1, 0] b.2) *
      Matrix.frobeniusNormSq
        (Matrix.quarterWeighted ![1] ![0, 1] (sourceBlock O b.2 b.1)) ≤ 1 := by
  apply weighted_source_block_sum_le_one ![1, 0] ![0, 1, 0] ![0, 1] ![1] O
  · intro i; fin_cases i <;> norm_num
  · intro l; fin_cases l <;> norm_num
  · intro t; fin_cases t <;> norm_num
  · intro u; fin_cases u; norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
  · exact hO

-- Zero covariance genuinely implies zero expected trace error, with unequal
-- private dimensions and no measurability assumption on the coefficients.
example (O : Matrix (Fin 1 × Fin 3) (Fin 1 × Fin 2) ℂ) (hO : ‖O‖ ≤ 1) :
    (∫ _w : Ω, Matrix.rectangularTraceNorm
      (weightedSourceError ![0, 1] ![1, 0, 0] O (fun _ ↦ 0)) ∂mu) ≤ 0 := by
  simpa only [Real.sqrt_zero] using
    integral_rectangularTraceNorm_weightedSourceError_le ![1] ![1] ![0, 1] ![1, 0, 0]
      O (fun _ _ ↦ 0) 0
      (by intro i; fin_cases i; norm_num)
      (by intro l; fin_cases l; norm_num)
      (by intro t; fin_cases t <;> norm_num)
      (by intro u; fin_cases u <;> norm_num)
      (by norm_num [Fin.sum_univ_succ]) (by norm_num [Fin.sum_univ_succ])
      (by norm_num [Fin.sum_univ_succ]) (by norm_num [Fin.sum_univ_succ])
      hO (by norm_num)
      (by intro b c; simp)
      (by intro b c; simp)

-- A common unrestricted phase needs only pair-product integrability for
-- nuclear measurability; no measurability premise on f is required.
example (f : Ω → ℂ)
    (hf : Integrable (fun w ↦ f w * conj (f w)) mu)
    (A : Matrix (Fin 3) (Fin 2) ℂ) :
    AEStronglyMeasurable
      (fun w ↦ Matrix.rectangularTraceNorm (∑ _ : Fin 1, f w • A)) mu := by
  exact aestronglyMeasurable_rectangularTraceNorm_sum (fun _ : Fin 1 ↦ f)
    (fun _ _ ↦ hf) (fun _ ↦ A)

-- The empty corrected-register sum is zero without imposing positive sizes.
example (O : Matrix (Fin 2 × Fin 3) (Fin 0 × Fin 1) ℂ)
    (tau : Fin 1 → ℝ) (tau' : Fin 3 → ℝ) (z : Fin 0 × Fin 2 → ℂ) :
    weightedSourceError tau tau' O z = 0 := by
  simp [weightedSourceError]
