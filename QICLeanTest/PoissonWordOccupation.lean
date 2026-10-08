/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordOccupation

/-! Retained-prefix occupation consumers, including a terminal-word counterexample. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal

namespace PoissonWordOccupationTest

-- Arbitrary nonnegative kernels require neither finiteness nor integrability.
example {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      F (partitionWords p (take w j)).1 (w.2 j) ∂measure ι T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫⁻ u, F u i ∂measure {i // p i} (Real.toNNReal s) :=
  lintegral_sum_partition_prefix p T F

example {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j)
        ∂measure ι T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ),
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
          ∫⁻ u, F u i ∂measure {i // p i} (Real.toNNReal s) :=
  lintegral_sum_omitted_partition_prefix p T F

-- Zero time annihilates arbitrary kernels, including infinite-valued ones.
example (p : Fin 3 → Prop) [DecidablePred p]
    (F : Word {i // p i} → Fin 3 → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      F (partitionWords p (take w j)).1 (w.2 j) ∂measure (Fin 3) 0) = 0 := by
  rw [lintegral_sum_partition_prefix]
  simp

example (p : Fin 3 → Prop) [DecidablePred p]
    (F : Word {i // p i} → Fin 3 → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j)
        ∂measure (Fin 3) 0) = 0 := by
  rw [lintegral_sum_omitted_partition_prefix]
  simp

-- An empty ambient alphabet has no marks at any duration.
example (T : ℝ≥0) (p : Fin 0 → Prop) [DecidablePred p]
    (F : Word {i // p i} → Fin 0 → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j)
        ∂measure (Fin 0) T) = 0 := by
  rw [lintegral_sum_omitted_partition_prefix]
  simp

-- Retaining every label gives zero occupation even when the kernel is infinity.
example (T : ℝ≥0) :
    (∫⁻ w : Word (Fin 3), ∑ j : Fin w.1,
      if (fun _ : Fin 3 => True) (w.2 j) then 0
      else (fun (_ : Word {_i : Fin 3 // True}) (_ : Fin 3) => (∞ : ℝ≥0∞))
        (partitionWords (fun _ : Fin 3 => True) (take w j)).1 (w.2 j)
        ∂measure (Fin 3) T) = 0 := by
  rw [lintegral_sum_omitted_partition_prefix (fun _ : Fin 3 => True) T (fun _ _ => ∞)]
  simp

-- Omitting every label recovers the ambient count rate.
example (T : ℝ≥0) :
    (∫⁻ w : Word (Fin 3), ∑ j : Fin w.1,
      if (fun _ : Fin 3 => False) (w.2 j) then (0 : ℝ≥0∞) else 1
        ∂measure (Fin 3) T) = 3 * T := by
  simpa using lintegral_omitted_count (fun _ : Fin 3 => False) T

-- For this split only label 1 is omitted, so its expected count is T.
example (T : ℝ≥0) :
    (∫⁻ w : Word (Fin 3), ∑ j : Fin w.1,
      if w.2 j ≠ 1 then (0 : ℝ≥0∞) else 1 ∂measure (Fin 3) T) = T := by
  have hcard : (Finset.univ.filter (fun i : Fin 3 => ¬i ≠ 1)).card = 1 := by decide
  simpa only [hcard, Nat.cast_one, one_mul] using
    lintegral_omitted_count (fun i : Fin 3 => i ≠ 1) T

-- The actual occupation law also handles an infinite kernel on an omitted label.
example :
    (∫⁻ w : Word (Fin 1), ∑ j : Fin w.1,
      if (fun _ : Fin 1 => False) (w.2 j) then 0
      else (fun (_ : Word {_i : Fin 1 // False}) (_ : Fin 1) => (∞ : ℝ≥0∞))
        (partitionWords (fun _ : Fin 1 => False) (take w j)).1 (w.2 j)
        ∂measure (Fin 1) 1) = ∞ := by
  simpa using lintegral_sum_omitted_partition_prefix
    (fun _ : Fin 1 => False) 1 (fun _ _ => ∞)

private def sample : Word (Fin 2) := List.equivSigmaTuple [1, 0, 1]

-- Only the first omitted 1 sees an empty retained prefix in [1, 0, 1].
private theorem sample_prefix_count : (∑ j : Fin sample.1,
    if sample.2 j = 0 then 0
    else if (partitionWords (fun i : Fin 2 => i = 0) (take sample j)).1.1 = 0
      then (1 : ℕ) else 0) = 1 := by
  decide

-- Replacing each prefix by the terminal retained word [0] incorrectly gives zero.
private theorem sample_terminal_count : (∑ j : Fin sample.1,
    if sample.2 j = 0 then 0
    else if (partitionWords (fun i : Fin 2 => i = 0) sample).1.1 = 0
      then (1 : ℕ) else 0) = 0 := by
  decide

-- The same distinction holds in the occupation law's extended nonnegative codomain.
example : (∑ j : Fin sample.1,
    if sample.2 j = 0 then 0
    else if (partitionWords (fun i : Fin 2 => i = 0) (take sample j)).1.1 = 0
      then (1 : ℝ≥0∞) else 0) = 1 := by
  exact_mod_cast sample_prefix_count

example : (∑ j : Fin sample.1,
    if sample.2 j = 0 then 0
    else if (partitionWords (fun i : Fin 2 => i = 0) sample).1.1 = 0
      then (1 : ℝ≥0∞) else 0) = 0 := by
  exact_mod_cast sample_terminal_count

end PoissonWordOccupationTest
