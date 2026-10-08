/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.WordMultiplicity
import QICLean.Probability.PoissonWord

/-!
# Count fibers of finite words

Every nonnegative count vector determines a finite, nonempty set of finite
words. Its cardinality is the multinomial coefficient. These are the actual
word fibers used in the fixed-time count and ordering calculation from
`09-amplification.tex`, lines 49–54 and 237–253; no chronological
clock process is constructed here.
-/

open scoped BigOperators Nat

namespace PoissonWord

variable {ι : Type*}

/-- The number of occurrences of each letter in a finite word. -/
noncomputable def countVector (w : Word ι) : ι → ℕ :=
  WordMultiplicity.countsFinsupp w.2

/-- The event that the word has the specified letter counts. -/
def countEvent (n : ι → ℕ) : Set (Word ι) := {w | countVector w = n}

/-- The words with the specified letter counts. -/
abbrev countFiber (n : ι → ℕ) := ↥(countEvent n)

@[simp] lemma countVector_nil : countVector (nil : Word ι) = 0 := by
  ext i
  simp [countVector, nil, WordMultiplicity.countsFinsupp]

variable [Fintype ι]

/-- The count vector determines the length of a word. -/
lemma sum_countVector (w : Word ι) : (∑ i, countVector w i) = w.1 :=
  WordMultiplicity.sum_counts w.2

lemma length_eq_sum_of_countVector_eq {w : Word ι} {n : ι → ℕ}
    (h : countVector w = n) : w.1 = ∑ i, n i := by
  rw [← h, sum_countVector]

/-- A count fiber is the corresponding set of words of length equal to the total count. -/
noncomputable def countFiberEquiv (n : ι → ℕ) :
    countFiber n ≃
      {w : Fin (∑ i, n i) → ι // (WordMultiplicity.countsFinsupp w : ι → ℕ) = n} :=
  (Equiv.ofBijective
    (fun w : {w : Fin (∑ i, n i) → ι //
        (WordMultiplicity.countsFinsupp w : ι → ℕ) = n} ↦
      (⟨⟨∑ i, n i, w.1⟩, w.2⟩ : countFiber n))
    ⟨by
      intro w v h
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
    , by
      rintro ⟨⟨m, w⟩, h⟩
      have hm : m = ∑ i, n i := length_eq_sum_of_countVector_eq h
      subst m
      exact ⟨⟨w, h⟩, rfl⟩⟩).symm

noncomputable instance instFintypeCountFiber (n : ι → ℕ) : Fintype (countFiber n) :=
  Fintype.ofEquiv _ (countFiberEquiv n).symm

omit [Fintype ι] in
/-- The count event is finite, even though all finite words form an infinite type. -/
lemma finite_countEvent [Finite ι] (n : ι → ℕ) : (countEvent n).Finite := by
  let := Fintype.ofFinite ι
  exact Set.toFinite _

/-- The cardinality of the count fiber is the multinomial coefficient. -/
lemma card_countFiber (n : ι → ℕ) :
    Fintype.card (countFiber n) = Nat.multinomial Finset.univ n := by
  rw [Fintype.card_congr (countFiberEquiv n), WordMultiplicity.card_counts_eq, ite_eq_left rfl]

/-- The factorial formula for the number of words with specified letter counts. -/
lemma card_countFiber_eq_factorial (n : ι → ℕ) :
    Fintype.card (countFiber n) = (∑ i, n i)! / ∏ i, (n i)! := by
  rw [card_countFiber, Nat.multinomial]

omit [Fintype ι] in
/-- Every count vector is attained by at least one finite word. -/
lemma countFiber_nonempty [Finite ι] (n : ι → ℕ) : Nonempty (countFiber n) := by
  let := Fintype.ofFinite ι
  apply Fintype.card_pos_iff.mp
  rw [card_countFiber]
  exact Nat.multinomial_pos _ _

omit [Fintype ι] in
/-- The count event is nonempty, including the zero vector and the empty alphabet. -/
lemma countEvent_nonempty [Finite ι] (n : ι → ℕ) : (countEvent n).Nonempty :=
  Set.nonempty_coe_sort.mp (countFiber_nonempty n)

end PoissonWord
