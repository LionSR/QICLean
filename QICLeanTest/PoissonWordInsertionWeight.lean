/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordInsertionWeight

/-! Strict consumers of the insertion-time scalar mass identity. -/

open MeasureTheory PoissonWord Set
open scoped ENNReal NNReal Nat

namespace PoissonWordInsertionWeightTest

-- Clipping to nonnegative time preserves measurability on the whole real line.
example (m : ℕ) : Measurable (fun s : ℝ ↦ weight (Fin 2) (Real.toNNReal s) m) :=
  measurable_weight_ofReal m

-- No positive-time hypothesis is needed.
example (m n : ℕ) :
    (∫ s : ℝ in 0..(0 : ℝ), weight (Fin 2) (Real.toNNReal s) m *
      weight (Fin 2) (Real.toNNReal (-s)) n) = weight (Fin 2) 0 (m + n + 1) := by
  simpa using integral_weight_mul_weight (ι := Fin 2) 0 m n

-- Empty alphabets are included in the scalar identity.
example (T : ℝ≥0) (m n : ℕ) :
    (∫ s : ℝ in 0..(T : ℝ), weight (Fin 0) (Real.toNNReal s) m *
      weight (Fin 0) (Real.toNNReal ((T : ℝ) - s)) n) =
      weight (Fin 0) T (m + n + 1) :=
  integral_weight_mul_weight T m n

-- Inserting one letter between two empty words yields the one-letter weight.
example (T : ℝ≥0) :
    (∫⁻ s : ℝ in Ioc 0 (T : ℝ),
      ENNReal.ofReal (weight (Fin 2) (Real.toNNReal s) 0) *
        ENNReal.ofReal (weight (Fin 2) (Real.toNNReal ((T : ℝ) - s)) 0)) =
      ENNReal.ofReal (weight (Fin 2) T 1) :=
  lintegral_weight_mul_weight T 0 0

-- Nontrivial prefix and suffix lengths retain their order in the mass identity.
example (T : ℝ≥0) :
    (∫⁻ s : ℝ in Ioc 0 (T : ℝ),
      ENNReal.ofReal (weight (Fin 3) (Real.toNNReal s) 2) *
        ENNReal.ofReal (weight (Fin 3) (Real.toNNReal ((T : ℝ) - s)) 4)) =
      ENNReal.ofReal (weight (Fin 3) T 7) :=
  lintegral_weight_mul_weight T 2 4

end PoissonWordInsertionWeightTest
