/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.CompressionSampling

/-! Compression sampling regressions for empty source sets, finite costs
and deterministic realizations on probability spaces. -/

open CompressionSampling MeasureTheory
open scoped BigOperators

example (Q ε : ℝ) : sampleCount 0 Q ε = 1 := by simp [sampleCount]

example (a : ℝ) :
    (∑ s ∈ (Finset.univ : Finset (Fin 2)).powerset.erase ∅, a ^ s.card) =
      2 * a + a ^ 2 := by
  rw [sum_nonempty_subsets_pow]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

example (Q ε : ℝ) (hε : 0 < ε) :
    (1 + Q / Real.sqrt (sampleCount 0 Q ε)) ^ (0 : ℕ) - 1 ≤ ε / 4 := by
  simp only [zero_slots_error]
  positivity

example {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (valid : Ω → Prop) (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    ∃ ω, valid ω ∧ ‖(0 : E)‖ ≤ ε / 2 := by
  simpa using exists_valid_norm_sum_le_half_sampleCount
    (μ := μ) (∅ : Finset (Fin 0)) (0 : ℝ) ε (by positivity) hε hε₁
    (fun _ _ ↦ (0 : E)) (by simp) (by simp) valid hvalid
