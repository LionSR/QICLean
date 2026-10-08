/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordRelabel

/-! Concrete alphabet changes, inverse transport, and degenerate word laws. -/

open MeasureTheory PoissonWord
open scoped NNReal

namespace PoissonWordRelabelTest

-- Swapping the two letters changes every occurrence without changing their order.
example :
    relabel (Equiv.swap (0 : Fin 2) 1) (List.equivSigmaTuple [0, 1, 0]) =
      List.equivSigmaTuple [1, 0, 1] := by
  apply congrArg (fun f : Fin 3 → Fin 2 => (⟨3, f⟩ : Word (Fin 2)))
  funext i
  fin_cases i <;> decide

-- The transport also works between distinct alphabet types.
example :
    relabel finTwoEquiv (List.equivSigmaTuple [(0 : Fin 2), 1, 0]) =
      List.equivSigmaTuple [false, true, false] := by
  apply congrArg (fun f : Fin 3 → Bool => (⟨3, f⟩ : Word Bool))
  funext i
  fin_cases i <;> decide

example (w : Word (Fin 2)) : (relabel finTwoEquiv w).1 = w.1 :=
  length_relabel finTwoEquiv w

example (w : Word (Fin 2)) : (relabel finTwoEquiv).symm (relabel finTwoEquiv w) = w :=
  (relabel finTwoEquiv).symm_apply_apply w

-- The actual law is transported, rather than merely its length distribution.
example (t : ℝ≥0) :
    (measure (Fin 2) t).map (relabel (Equiv.swap (0 : Fin 2) 1)) =
      measure (Fin 2) t :=
  map_relabel (Equiv.swap (0 : Fin 2) 1) t

example (t : ℝ≥0) :
    MeasurePreserving (relabel finTwoEquiv) (measure (Fin 2) t) (measure Bool t) :=
  measurePreserving_relabel finTwoEquiv t

-- Empty alphabets can be transported between different empty types.
example (t : ℝ≥0) :
    (measure (Fin 0) t).map (relabel finZeroEquiv) =
      Measure.dirac (nil : Word Empty) := by
  rw [map_relabel, measure_of_isEmpty]

example :
    (measure (Fin 2) 0).map (relabel finTwoEquiv) =
      Measure.dirac (nil : Word Bool) := by
  rw [map_relabel, measure_zero]

end PoissonWordRelabelTest
