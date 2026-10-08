/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordCounts

/-! Nontrivial multiplicities and degenerate alphabets for actual word fibers. -/

open PoissonWord
open scoped BigOperators Nat

namespace PoissonWordCountsTest

-- The count map counts actual positions, retaining repeated labels.
example : countVector (⟨3, ![0, 1, 0]⟩ : Word (Fin 2)) = ![2, 1] := by
  ext i
  fin_cases i <;>
    simp [countVector, WordMultiplicity.countsFinsupp, Fin.sum_univ_three]

-- Repeating one label twice and a second label once gives three orderings.
example : Fintype.card (countFiber ![2, 1]) = 3 := by
  rw [card_countFiber_eq_factorial]
  norm_num [Fin.sum_univ_two, Fin.prod_univ_two]

-- Multiplicities two and two give six orderings.
example : Fintype.card (countFiber ![2, 2]) = 6 := by
  rw [card_countFiber_eq_factorial]
  norm_num [Fin.sum_univ_two, Fin.prod_univ_two]

-- Prescribing the wrong total count gives no words of that fixed length.
example : Fintype.card {w : Fin 2 → Fin 2 //
    (WordMultiplicity.countsFinsupp w : Fin 2 → ℕ) = ![2, 1]} = 0 := by
  rw [WordMultiplicity.card_counts_eq]
  norm_num [Fin.sum_univ_two]

-- The zero count fiber consists of one word for every finite alphabet.
example {ι : Type*} [Fintype ι] : Fintype.card (countFiber (0 : ι → ℕ)) = 1 := by
  rw [card_countFiber_eq_factorial]
  simp

-- Every count vector on the empty alphabet has exactly one word.
example (n : Fin 0 → ℕ) : Fintype.card (countFiber n) = 1 := by
  rw [card_countFiber_eq_factorial]
  simp

-- The empty alphabet has no positive-length words, even for its unique count vector.
example : Fintype.card {w : Fin 1 → Fin 0 //
    (WordMultiplicity.countsFinsupp w : Fin 0 → ℕ) = 0} = 0 := by
  rw [WordMultiplicity.card_counts_eq]
  simp

-- Count fibers remain finite and attained before selecting any time parameter.
example {ι : Type*} [Finite ι] (n : ι → ℕ) :
    (countEvent n).Finite ∧ (countEvent n).Nonempty :=
  ⟨finite_countEvent n, countEvent_nonempty n⟩

end PoissonWordCountsTest
