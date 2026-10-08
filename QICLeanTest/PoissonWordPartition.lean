/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordPartition

/-! Ordered predicate splitting, concrete product laws, and degenerate predicates. -/

open MeasureTheory PoissonWord
open scoped NNReal

namespace PoissonWordPartitionTest

-- A nonmonotone word with repetitions tests positions, not just label counts.
example :
    (List.ofFn (partitionWords (fun i : Fin 3 => i ≠ 1)
      (List.equivSigmaTuple [2, 1, 0, 2, 1])).1.2).map Subtype.val = [2, 0, 2] := by
  rw [ofFn_partitionWords_fst]
  decide

example :
    (List.ofFn (partitionWords (fun i : Fin 3 => i ≠ 1)
      (List.equivSigmaTuple [2, 1, 0, 2, 1])).2.2).map Subtype.val = [1, 1] := by
  rw [ofFn_partitionWords_snd]
  decide

-- Sorting the selected labels would be an incorrect implementation.
example :
    (List.ofFn (partitionWords (fun i : Fin 3 => i ≠ 1)
      (List.equivSigmaTuple [2, 1, 0, 2, 1])).1.2).map Subtype.val ≠ [0, 2, 2] := by
  rw [ofFn_partitionWords_fst]
  decide

example (w : Word (Fin 3)) :
    (partitionWords (fun i : Fin 3 => i ≠ 1) w).1.1 +
      (partitionWords (fun i : Fin 3 => i ≠ 1) w).2.1 = w.1 :=
  partitionWords_length (fun i : Fin 3 => i ≠ 1) w

-- Constant predicates retain the full ordered word on precisely one side.
example (w : Word (Fin 3)) :
    (List.ofFn (partitionWords (fun _ : Fin 3 => True) w).1.2).map Subtype.val =
      List.ofFn w.2 := by
  rw [ofFn_partitionWords_fst]
  simp

example (w : Word (Fin 3)) :
    (List.ofFn (partitionWords (fun _ : Fin 3 => True) w).2.2).map Subtype.val = [] := by
  rw [ofFn_partitionWords_snd]
  simp

example (w : Word (Fin 3)) :
    (List.ofFn (partitionWords (fun _ : Fin 3 => False) w).1.2).map Subtype.val = [] := by
  rw [ofFn_partitionWords_fst]
  simp

example (w : Word (Fin 3)) :
    (List.ofFn (partitionWords (fun _ : Fin 3 => False) w).2.2).map Subtype.val =
      List.ofFn w.2 := by
  rw [ofFn_partitionWords_snd]
  simp

-- Both ordered subwords come from one full sample and have the actual product law.
example (t : ℝ≥0) :
    (measure (Fin 3) t).map (partitionWords (fun i : Fin 3 => i ≠ 1)) =
      (measure {i : Fin 3 // i ≠ 1} t).prod (measure {i : Fin 3 // ¬i ≠ 1} t) :=
  map_partitionWords (fun i : Fin 3 => i ≠ 1) t

example (t : ℝ≥0) :
    ProbabilityTheory.IndepFun
      (fun w => (partitionWords (fun i : Fin 3 => i ≠ 1) w).1)
      (fun w => (partitionWords (fun i : Fin 3 => i ≠ 1) w).2) (measure (Fin 3) t) :=
  indepFun_partitionWords (fun i : Fin 3 => i ≠ 1) t

-- The empty-pair atom sees the two distinct alphabet rates, two and one.
example (t : ℝ≥0) :
    ((measure (Fin 3) t).map (partitionWords (fun i : Fin 3 => i ≠ 1))) {(nil, nil)} =
      ENNReal.ofReal (Real.exp (-2 * (t : ℝ))) *
        ENNReal.ofReal (Real.exp (-(t : ℝ))) := by
  rw [map_partitionWords, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PoissonWord.measure_singleton, PoissonWord.measure_singleton]
  have hselected : Fintype.card {i : Fin 3 // i ≠ 1} = 2 := by decide
  simp [weight, hselected, nil]

-- Empty predicate alphabets need no positive-cardinality hypothesis.
example (t : ℝ≥0) :
    (measure (Fin 3) t).map (fun w => (partitionWords (fun _ : Fin 3 => False) w).1) =
      Measure.dirac (nil : Word {_i : Fin 3 // False}) := by
  rw [map_partitionWords_fst, measure_of_isEmpty]

example (t : ℝ≥0) :
    (measure (Fin 3) t).map (fun w => (partitionWords (fun _ : Fin 3 => True) w).2) =
      Measure.dirac (nil : Word {_i : Fin 3 // ¬True}) := by
  let : IsEmpty {_i : Fin 3 // ¬True} := ⟨fun i => i.2 trivial⟩
  rw [map_partitionWords_snd, measure_of_isEmpty]

-- Time zero gives a pair of empty words even for a nontrivial predicate.
example :
    (measure (Fin 3) 0).map (partitionWords (fun i : Fin 3 => i ≠ 1)) =
      (Measure.dirac (nil : Word {i : Fin 3 // i ≠ 1})).prod
        (Measure.dirac (nil : Word {i : Fin 3 // ¬i ≠ 1})) := by
  rw [map_partitionWords, measure_zero, measure_zero]

example (t : ℝ≥0) :
    (measure (Fin 0) t).map (partitionWords (fun i : Fin 0 => i ≠ i)) =
      (Measure.dirac (nil : Word {i : Fin 0 // i ≠ i})).prod
        (Measure.dirac (nil : Word {i : Fin 0 // ¬i ≠ i})) := by
  rw [map_partitionWords, measure_of_isEmpty, measure_of_isEmpty]

end PoissonWordPartitionTest
