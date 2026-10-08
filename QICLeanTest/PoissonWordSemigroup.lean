/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordSemigroup

/-! Strict consumers of time composition of the actual word measures. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal Nat

namespace PoissonWordSemigroupTest

-- Two independently sampled binary words concatenate with the sum-time law.
example (s t : ℝ≥0) :
    ((measure (Fin 2) s).prod (measure (Fin 2) t)).map
        (fun p ↦ append p.1 p.2) = measure (Fin 2) (s + t) :=
  map_append s t

-- Time zero is a left and a right identity without a positivity assumption.
example (t : ℝ≥0) :
    ((measure (Fin 2) 0).prod (measure (Fin 2) t)).map
        (fun p ↦ append p.1 p.2) = measure (Fin 2) t := by
  simpa using map_append (ι := Fin 2) 0 t

example (t : ℝ≥0) :
    ((measure (Fin 2) t).prod (measure (Fin 2) 0)).map
        (fun p ↦ append p.1 p.2) = measure (Fin 2) t := by
  simpa using map_append (ι := Fin 2) t 0

-- An empty alphabet still gives the same probability convolution law.
example (s t : ℝ≥0) :
    ((measure (Fin 0) s).prod (measure (Fin 0) t)).map
        (fun p ↦ append p.1 p.2) = measure (Fin 0) (s + t) :=
  map_append s t

-- A one-letter word has exactly the two endpoint decompositions.
example (s t : ℝ≥0) :
    weight (Fin 2) s 0 * weight (Fin 2) t 1 +
        weight (Fin 2) s 1 * weight (Fin 2) t 0 = weight (Fin 2) (s + t) 1 := by
  simpa [Fin.sum_univ_two] using sum_weight_mul_weight (ι := Fin 2) s t 1

-- The empty word has one decomposition; its masses multiply.
example (s t : ℝ≥0) :
    weight (Fin 2) s 0 * weight (Fin 2) t 0 = weight (Fin 2) (s + t) 0 := by
  simpa using sum_weight_mul_weight (ι := Fin 2) s t 0

-- The actual preimage fiber has the correct mass for a specified nonempty word.
example (s t : ℝ≥0) (a : Fin 2) :
    ((measure (Fin 2) s).prod (measure (Fin 2) t))
        ((fun p ↦ append p.1 p.2) ⁻¹' {(⟨1, fun _ ↦ a⟩ : Word (Fin 2))}) =
      ENNReal.ofReal (weight (Fin 2) (s + t) 1) :=
  prod_measure_append_preimage_singleton s t ⟨1, fun _ ↦ a⟩

end PoissonWordSemigroupTest
