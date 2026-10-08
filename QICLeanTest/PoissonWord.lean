/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWord

/-! Finite alphabets and degenerate-time consumers of the atomic word law. -/

open MeasureTheory PoissonWord
open scoped BigOperators NNReal Nat

namespace PoissonWordTest

-- Two distinct labels give total clock rate twice the elapsed time.
example (t : ℝ≥0) :
    (measure (Fin 2) t).map (fun w ↦ w.1) =
      ProbabilityTheory.poissonMeasure (2 * t) := by
  simpa using map_length (ι := Fin 2) t

-- Every two-letter word has the same mass, without normalization hypotheses.
example (t : ℝ≥0) (w : Fin 2 → Fin 2) :
    measure (Fin 2) t {⟨2, w⟩} =
      ENNReal.ofReal (Real.exp (-2 * (t : ℝ)) * (t : ℝ) ^ 2 / 2) := by
  simpa [weight] using measure_singleton t (⟨2, w⟩ : Word (Fin 2))

-- There is an empty word even when the alphabet itself is empty.
example (t : ℝ≥0) : measure (Fin 0) t = Measure.dirac (nil : Word (Fin 0)) :=
  measure_of_isEmpty t

-- At zero time, the law on any finite alphabet is concentrated at that word.
example : measure (Fin 3) 0 = Measure.dirac (nil : Word (Fin 3)) := measure_zero

-- The mass is really one, rather than assumed by a probabilistic wrapper.
example (t : ℝ≥0) : measure (Fin 2) t Set.univ = 1 := measure_univ

-- A constant observable has expectation one under the constructed measure.
example (t : ℝ≥0) : (∫ _w : Word (Fin 2), (1 : ℝ) ∂measure (Fin 2) t) = 1 := by
  simp

-- Vanishing finite-word sums give a zero expectation and are integrable.
example (t : ℝ≥0) :
    Integrable (fun _w : Word (Fin 2) ↦ (0 : ℝ)) (measure (Fin 2) t) ∧
      (∫ _w : Word (Fin 2), (0 : ℝ) ∂measure (Fin 2) t) ≤ 0 := by
  simpa using integrable_and_integral_le_of_sum_le_pow t
    (fun _w : Word (Fin 2) ↦ (0 : ℝ)) (fun _ ↦ le_rfl)
    (a := 0) (C := 0) le_rfl le_rfl (fun _ ↦ by simp)

-- A genuine strict geometric layer bound gives rate-one decay for two labels.
example (t : ℝ≥0) (f : Word (Fin 2) → ℝ) (hf : ∀ w, 0 ≤ f w)
    (hbound : ∀ m, (∑ w : Fin m → Fin 2, f ⟨m, w⟩) ≤ (1 : ℝ) ^ m * 3) :
    Integrable f (measure (Fin 2) t) ∧
      (∫ w, f w ∂measure (Fin 2) t) ≤ Real.exp (-(t : ℝ)) * 3 := by
  simpa using integrable_and_integral_le_of_sum_le_pow t f hf
    (a := 1) (C := 3) (by norm_num) (by norm_num) hbound

end PoissonWordTest
