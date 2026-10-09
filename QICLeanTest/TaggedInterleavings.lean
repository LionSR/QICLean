/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TaggedInterleavings

/-! Tagged words retain their order and multiplicities, including infinite alphabets. -/

open TaggedInterleavings

namespace TaggedInterleavingsTest

-- Repeated letters give distinct tagged words, one for each position of the right tag.
example : taggedInterleavings [7, 7] [7] =
    [[Sum.inl 7, Sum.inl 7, Sum.inr 7],
      [Sum.inl 7, Sum.inr 7, Sum.inl 7],
      [Sum.inr 7, Sum.inl 7, Sum.inl 7]] := by
  simp [taggedInterleavings]

-- A shuffle cannot reverse either prescribed word.
example : [Sum.inl 2, Sum.inr 9, Sum.inl 1] ∉ taggedInterleavings [1, 2] [9] := by
  simp [taggedInterleavings]

-- Overlapping numerical labels remain distinguished by their tags.
example : [Sum.inr 4, Sum.inl 4] ∈ taggedInterleavings [4] [4] := by
  simp [taggedInterleavings]

-- No decidable equality or finite alphabet is needed, even with repeated functions.
example (f g : ℕ → ℕ) :
    (taggedInterleavings [f, f] [g, g]).Nodup ∧
      (taggedInterleavings [f, f] [g, g]).length = 6 := by
  refine ⟨nodup_taggedInterleavings _ _, ?_⟩
  rw [length_taggedInterleavings]
  change Nat.choose 4 2 = 6
  decide

-- The only shuffle with an empty left word is the tagged right word.
example (ys : List ℕ) : taggedInterleavings ([] : List Empty) ys = [ys.map Sum.inr] := by
  rw [taggedInterleavings]

-- The only shuffle with an empty right word is the tagged left word.
example (xs : List ℕ) : taggedInterleavings xs ([] : List Empty) = [xs.map Sum.inl] := by
  cases xs <;> simp [taggedInterleavings]

example : taggedInterleavings ([] : List Empty) ([] : List Empty) = [[]] := by
  simp [taggedInterleavings]

-- Prescribed filtered words determine every fiber word's total length.
example {ι κ : Type*} (xs : List ι) (ys : List κ) (w : List (ι ⊕ κ))
    (hl : w.filterMap Sum.getLeft? = xs) (hr : w.filterMap Sum.getRight? = ys) :
    w.length = xs.length + ys.length := by
  exact length_of_mem_taggedInterleavings ((mem_taggedInterleavings_iff xs ys w).mpr ⟨hl, hr⟩)

end TaggedInterleavingsTest
