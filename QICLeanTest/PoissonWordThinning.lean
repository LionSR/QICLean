/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordThinning

/-! Ordered-word thinning, repeated letters, empty alphabets, and zero-time cases. -/

open MeasureTheory PoissonWord
open scoped NNReal

namespace PoissonWordThinningTest

-- The retained order distinguishes this coupling from a mere count-vector law.
example :
    leftWord (List.equivSigmaTuple
      [Sum.inl (1 : Fin 2), Sum.inr true, Sum.inl 0, Sum.inr false, Sum.inl 1]) =
      List.equivSigmaTuple [1, 0, 1] := by
  simp [leftWord, List.filterMap, Sum.getLeft?]

example :
    rightWord (List.equivSigmaTuple
      [Sum.inl (1 : Fin 2), Sum.inr true, Sum.inl 0, Sum.inr false, Sum.inl 1]) =
      List.equivSigmaTuple [true, false] := by
  simp [rightWord, List.filterMap, Sum.getRight?]

-- Repetitions within both alphabets do not collapse the six tagged interleavings.
example :
    Fintype.card (thinningFiber (List.equivSigmaTuple [true, true])
      (List.equivSigmaTuple [(0 : Fin 1), 0])) = 6 := by
  rw [card_thinningFiber]
  decide

example (w : Word (Bool ⊕ Fin 1))
    (h : w ∈ thinningEvent (List.equivSigmaTuple [true, true])
      (List.equivSigmaTuple [(0 : Fin 1), 0])) : w.1 = 4 := by
  exact length_eq_add_of_mem_thinningEvent h

-- The product law applies to full ordered words over unequal finite alphabets.
example (t : ℝ≥0) :
    (measure (Fin 2 ⊕ Fin 3) t).map (fun w ↦ (leftWord w, rightWord w)) =
      (measure (Fin 2) t).prod (measure (Fin 3) t) :=
  map_leftWord_rightWord t

example (t : ℝ≥0) :
    ProbabilityTheory.IndepFun (leftWord (ι := Fin 2) (κ := Fin 3)) rightWord
      (measure (Fin 2 ⊕ Fin 3) t) :=
  indepFun_leftWord_rightWord t

-- The event for repeated retained letters and one omitted letter has product mass.
example (t : ℝ≥0) :
    measure (Bool ⊕ Fin 1) t
      (thinningEvent (List.equivSigmaTuple [true, true])
        (List.equivSigmaTuple [(0 : Fin 1)])) =
      ENNReal.ofReal (Real.exp (-2 * (t : ℝ)) * (t : ℝ) ^ 2 / 2) *
        ENNReal.ofReal (Real.exp (-(t : ℝ)) * (t : ℝ)) := by
  simpa [PoissonWord.measure_singleton, weight, List.equivSigmaTuple] using
    measure_thinningEvent_eq_mul t (List.equivSigmaTuple [true, true])
      (List.equivSigmaTuple [(0 : Fin 1)])

-- An empty retained alphabet always produces the empty word.
example (t : ℝ≥0) :
    (measure (Fin 0 ⊕ Fin 2) t).map leftWord =
      Measure.dirac (nil : Word (Fin 0)) := by
  rw [map_leftWord, measure_of_isEmpty]

-- The other marginal still has its complete ordered-word law.
example (t : ℝ≥0) :
    (measure (Fin 0 ⊕ Fin 2) t).map rightWord = measure (Fin 2) t :=
  map_rightWord t

example (t : ℝ≥0) :
    (measure (Fin 2 ⊕ Fin 0) t).map (fun w ↦ (leftWord w, rightWord w)) =
      (measure (Fin 2) t).prod (Measure.dirac (nil : Word (Fin 0))) := by
  rw [map_leftWord_rightWord, measure_of_isEmpty (ι := Fin 0)]

-- Both alphabets may be empty.
example (t : ℝ≥0) :
    (measure (Fin 0 ⊕ Fin 0) t).map (fun w ↦ (leftWord w, rightWord w)) =
      (Measure.dirac (nil : Word (Fin 0))).prod (Measure.dirac (nil : Word (Fin 0))) := by
  simp only [map_leftWord_rightWord, measure_of_isEmpty (ι := Fin 0)]

-- Time zero needs no positivity premise or cancellation of a time power.
example :
    (measure (Fin 2 ⊕ Fin 3) 0).map (fun w ↦ (leftWord w, rightWord w)) =
      (Measure.dirac (nil : Word (Fin 2))).prod (Measure.dirac (nil : Word (Fin 3))) := by
  rw [map_leftWord_rightWord, measure_zero, measure_zero]

example (m n : ℕ) :
    (Nat.choose (m + n) m : ℝ) * weight (Fin 2 ⊕ Fin 3) 0 (m + n) =
      weight (Fin 2) 0 m * weight (Fin 3) 0 n :=
  choose_mul_weight_sum 0 m n

end PoissonWordThinningTest
