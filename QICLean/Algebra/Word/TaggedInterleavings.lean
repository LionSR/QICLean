/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sum.Basic

/-!
# Tagged interleavings of two words

The order-preserving interleavings of two words over disjoint tagged alphabets
form a concrete duplicate-free list. Its members are precisely the words with
the prescribed left and right filtered words, and its length is the binomial
coefficient. The alphabets may be infinite and either word may repeat letters.
-/

namespace TaggedInterleavings

variable {ι κ : Type*}

/-- All order-preserving interleavings, retaining the origin of every letter. -/
def taggedInterleavings : List ι → List κ → List (List (ι ⊕ κ))
  | [], ys => [ys.map Sum.inr]
  | xs, [] => [xs.map Sum.inl]
  | x :: xs, y :: ys =>
      (taggedInterleavings xs (y :: ys)).map (Sum.inl x :: ·) ++
        (taggedInterleavings (x :: xs) ys).map (Sum.inr y :: ·)
termination_by xs ys => xs.length + ys.length

private lemma filters_eq_nil_left (w : List (ι ⊕ κ)) (ys : List κ) :
    (w.filterMap Sum.getLeft? = [] ∧ w.filterMap Sum.getRight? = ys) ↔
      w = ys.map Sum.inr := by
  induction w generalizing ys with
  | nil => cases ys <;> simp
  | cons a w ih =>
      cases a with
      | inl a => cases ys <;> simp
      | inr a => cases ys <;> simp_all [and_left_comm]

private lemma filters_eq_nil_right (w : List (ι ⊕ κ)) (xs : List ι) :
    (w.filterMap Sum.getLeft? = xs ∧ w.filterMap Sum.getRight? = []) ↔
      w = xs.map Sum.inl := by
  induction w generalizing xs with
  | nil => cases xs <;> simp
  | cons a w ih =>
      cases a with
      | inl a => cases xs <;> simp_all [and_assoc]
      | inr a => cases xs <;> simp

/-- Membership is characterized by the two filtered words. -/
lemma mem_taggedInterleavings_iff (xs : List ι) (ys : List κ) (w : List (ι ⊕ κ)) :
    w ∈ taggedInterleavings xs ys ↔
      w.filterMap Sum.getLeft? = xs ∧ w.filterMap Sum.getRight? = ys := by
  induction xs generalizing ys w with
  | nil => rw [filters_eq_nil_left]; simp only [taggedInterleavings, List.mem_singleton]
  | cons x xs ihx =>
      induction ys generalizing w with
      | nil => rw [filters_eq_nil_right]; simp only [taggedInterleavings, List.mem_singleton]
      | cons y ys ihy =>
          rw [taggedInterleavings]
          cases w with
          | nil => simp
          | cons a w =>
              cases a <;>
                simp [List.filterMap_cons, Sum.getLeft?, Sum.getRight?, ihx, ihy, and_assoc,
                  and_comm, and_left_comm, eq_comm]

/-- The enumeration has no repetitions, even when the prescribed words do. -/
lemma nodup_taggedInterleavings (xs : List ι) (ys : List κ) :
    (taggedInterleavings xs ys).Nodup := by
  induction xs generalizing ys with
  | nil => simp [taggedInterleavings]
  | cons x xs ihx =>
      induction ys with
      | nil => simp [taggedInterleavings]
      | cons y ys ihy =>
          rw [taggedInterleavings]
          apply List.Nodup.append
          · exact (ihx (y :: ys)).map (fun _ _ h ↦ (List.cons.inj h).2)
          · exact ihy.map (fun _ _ h ↦ (List.cons.inj h).2)
          · simp [List.disjoint_left]

/-- Choosing the positions occupied by the left word counts the interleavings. -/
lemma length_taggedInterleavings (xs : List ι) (ys : List κ) :
    (taggedInterleavings xs ys).length =
      Nat.choose (xs.length + ys.length) xs.length := by
  induction xs generalizing ys with
  | nil => simp [taggedInterleavings]
  | cons x xs ihx =>
      induction ys with
      | nil => simp [taggedInterleavings]
      | cons y ys ihy =>
          simp only [taggedInterleavings, List.length_append, List.length_map]
          rw [ihx, ihy]
          simp only [List.length_cons]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.choose_succ_succ (xs.length + ys.length + 1) xs.length).symm

/-- Filtering by the two tags partitions the positions of a word. -/
lemma length_filterMap_add (w : List (ι ⊕ κ)) :
    (w.filterMap Sum.getLeft?).length + (w.filterMap Sum.getRight?).length = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases a <;>
        simp [List.filterMap_cons, Sum.getLeft?, Sum.getRight?, ← ih, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]

/-- Every interleaving has the sum of the two prescribed lengths. -/
lemma length_of_mem_taggedInterleavings {xs : List ι} {ys : List κ} {w : List (ι ⊕ κ)}
    (h : w ∈ taggedInterleavings xs ys) : w.length = xs.length + ys.length := by
  obtain ⟨hl, hr⟩ := (mem_taggedInterleavings_iff xs ys w).mp h
  rw [← length_filterMap_add w, hl, hr]

end TaggedInterleavings
