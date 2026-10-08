/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordIndependentCounts

/-! Strict consumers of the count law, including the degenerate cases. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal Nat

namespace PoissonWordIndependentCountsTest

-- This is a pushforward of the actual word measure, with no independence hypothesis.
example (t : ℝ≥0) :
    (measure (Fin 2) t).map countVector =
      Measure.pi (fun _ : Fin 2 ↦ ProbabilityTheory.poissonMeasure t) :=
  map_countVector t

-- Each individual clock count has rate t, rather than the total rate 2t.
example (t : ℝ≥0) :
    (measure (Fin 2) t).map (fun w ↦ countVector w 0) =
      ProbabilityTheory.poissonMeasure t :=
  map_countVector_apply t 0

-- Independence is proved from the same word law.
example (t : ℝ≥0) :
    ProbabilityTheory.iIndepFun (fun i w ↦ countVector w i) (measure (Fin 3) t) :=
  iIndepFun_countVector t

-- A singleton alphabet and an empty alphabet satisfy the same theorem.
example (t : ℝ≥0) :
    (measure (Fin 1) t).map countVector =
      Measure.pi (fun _ : Fin 1 ↦ ProbabilityTheory.poissonMeasure t) :=
  map_countVector t

example (t : ℝ≥0) :
    (measure (Fin 0) t).map countVector =
      Measure.pi (fun _ : Fin 0 ↦ ProbabilityTheory.poissonMeasure t) :=
  map_countVector t

-- Zero time is included directly, with no division by t or positivity assumption.
example :
    (measure (Fin 2) 0).map countVector =
      Measure.pi (fun _ : Fin 2 ↦ ProbabilityTheory.poissonMeasure 0) :=
  map_countVector 0

-- Summing singleton weights over a count fiber uses its actual finite cardinality.
example (t : ℝ≥0) (n : Fin 2 → ℕ) :
    measure (Fin 2) t (countEvent n) = (Fintype.card (countFiber n) : ℝ≥0∞) *
      ENNReal.ofReal (weight (Fin 2) t (∑ i, n i)) :=
  measure_countEvent t n

-- The same fiber mass factors into two Poisson singleton masses.
example (t : ℝ≥0) (n : Fin 2 → ℕ) :
    measure (Fin 2) t (countEvent n) =
      ProbabilityTheory.poissonMeasure t {n 0} *
        ProbabilityTheory.poissonMeasure t {n 1} := by
  simpa [Fin.prod_univ_two] using measure_countEvent_eq_prod t n

-- Positive counts have zero mass at time zero.
example : measure (Fin 2) 0 (countEvent (fun _ ↦ 1)) = 0 := by
  rw [measure_countEvent_eq_prod]
  simp [ProbabilityTheory.poissonMeasure_singleton]

-- With no labels, the unique count event has probability one at every time.
example (t : ℝ≥0) : measure (Fin 0) t (countEvent (fun i ↦ Fin.elim0 i)) = 1 := by
  rw [measure_countEvent_eq_prod]
  simp

end PoissonWordIndependentCountsTest
