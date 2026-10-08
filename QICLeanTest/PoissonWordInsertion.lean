/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordInsertion

/-! Strict consumers of insertion into the actual Poissonized word measures. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal

namespace PoissonWordInsertionTest

-- An arbitrary kernel needs no finiteness or integrability assumption.
example (T : ℝ≥0) (F : Word (Fin 2) → Fin 2 → Word (Fin 2) → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) (drop w (j + 1))
      ∂measure (Fin 2) T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : Fin 2,
        ∫⁻ u, ∫⁻ v, F u i v ∂measure (Fin 2) (Real.toNNReal ((T : ℝ) - s))
          ∂measure (Fin 2) (Real.toNNReal s) :=
  lintegral_sum_marked T F

-- Zero time still gives zero when the kernel can take the value infinity.
example (F : Word (Fin 2) → Fin 2 → Word (Fin 2) → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) (drop w (j + 1))
      ∂measure (Fin 2) 0) = 0 := by
  rw [lintegral_sum_marked]
  simp

-- The empty alphabet has no marked positions at any duration.
example (T : ℝ≥0) (F : Word (Fin 0) → Fin 0 → Word (Fin 0) → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) (drop w (j + 1))
      ∂measure (Fin 0) T) = 0 := by
  rw [lintegral_sum_marked]
  simp

-- Integrating out the suffix leaves exactly the prefix law at time s.
example (T : ℝ≥0) (F : Word (Fin 2) → Fin 2 → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure (Fin 2) T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : Fin 2,
        ∫⁻ u, F u i ∂measure (Fin 2) (Real.toNNReal s) :=
  lintegral_sum_prefix T F

-- The constant-one kernel counts positions, including repeated letters.
example (T : ℝ≥0) :
    (∫⁻ w : Word (Fin 2), (w.1 : ℝ≥0∞) ∂measure (Fin 2) T) = 2 * T := by
  simpa using lintegral_length (ι := Fin 2) T

-- A positive duration and an infinite-valued one-letter kernel give infinity.
example :
    (∫⁻ w : Word (Fin 1), ∑ _j : Fin w.1, (∞ : ℝ≥0∞) ∂measure (Fin 1) 1) = ∞ := by
  simpa using lintegral_sum_prefix (ι := Fin 1) 1 (fun _ _ ↦ ∞)

end PoissonWordInsertionTest
