/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWord
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card

/-!
# Concatenation of finite words

Concatenation is associative with the empty word as identity. Its fiber over
a word of length `m` consists of precisely the `m + 1` prefix/suffix splits.
The equivalence `appendFiberEquiv` constructs every split and proves uniqueness;
no finiteness assumption on the alphabet is needed.
-/

namespace PoissonWord

variable {ι : Type*}

/-- Concatenate two words in their original order. -/
def append (u v : Word ι) : Word ι := ⟨u.1 + v.1, Fin.append u.2 v.2⟩

@[simp] lemma length_append (u v : Word ι) : (append u v).1 = u.1 + v.1 := rfl

@[simp] lemma nil_append (w : Word ι) : append nil w = w := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (append nil w).2 = List.ofFn w.2
  simp only [append, List.ofFn_fin_append, nil, List.ofFn_zero, List.nil_append]

@[simp] lemma append_nil (w : Word ι) : append w nil = w := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (append w nil).2 = List.ofFn w.2
  simp only [append, List.ofFn_fin_append, nil, List.ofFn_zero, List.append_nil]

lemma append_assoc (u v w : Word ι) : append (append u v) w = append u (append v w) := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (append (append u v) w).2 = List.ofFn (append u (append v w)).2
  simp only [append, List.ofFn_fin_append, List.append_assoc]

/-- The first `k` letters, or the entire word when `k` exceeds its length. -/
def take (w : Word ι) (k : ℕ) : Word ι :=
  List.equivSigmaTuple ((List.ofFn w.2).take k)

/-- The remaining letters after removing the first `k` letters. -/
def drop (w : Word ι) (k : ℕ) : Word ι :=
  List.equivSigmaTuple ((List.ofFn w.2).drop k)

@[simp] lemma length_take (w : Word ι) (k : ℕ) : (take w k).1 = min k w.1 := by
  simp [take, List.equivSigmaTuple]

@[simp] lemma length_drop (w : Word ι) (k : ℕ) : (drop w k).1 = w.1 - k := by
  simp [drop, List.equivSigmaTuple]

lemma length_take_of_le (w : Word ι) {k : ℕ} (hk : k ≤ w.1) : (take w k).1 = k := by
  rw [length_take, min_eq_left hk]

@[simp] lemma ofFn_take (w : Word ι) (k : ℕ) :
    List.ofFn (take w k).2 = (List.ofFn w.2).take k := by
  simp [take, List.equivSigmaTuple]

@[simp] lemma ofFn_drop (w : Word ι) (k : ℕ) :
    List.ofFn (drop w k).2 = (List.ofFn w.2).drop k := by
  simp [drop, List.equivSigmaTuple]

@[simp] lemma append_take_drop (w : Word ι) (k : ℕ) :
    append (take w k) (drop w k) = w := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (append (take w k) (drop w k)).2 = List.ofFn w.2
  simp only [append, List.ofFn_fin_append, ofFn_take, ofFn_drop, List.take_append_drop]

@[simp] lemma take_append (u v : Word ι) : take (append u v) u.1 = u := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (take (append u v) u.1).2 = List.ofFn u.2
  simpa only [ofFn_take, append, List.ofFn_fin_append, List.length_ofFn] using
    (List.take_append_length (l₁ := List.ofFn u.2) (l₂ := List.ofFn v.2))

@[simp] lemma drop_append (u v : Word ι) : drop (append u v) u.1 = v := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (drop (append u v) u.1).2 = List.ofFn v.2
  simp [append]

/-- The actual pairs of words whose concatenation is the specified word. -/
abbrev appendFiber (w : Word ι) := {p : Word ι × Word ι // append p.1 p.2 = w}

/-- A concatenation fiber is parametrized by the length of the prefix. -/
def appendFiberEquiv (w : Word ι) : appendFiber w ≃ Fin (w.1 + 1) where
  toFun p := ⟨p.1.1.1, by
    have h := congrArg Sigma.fst p.2
    change p.1.1.1 + p.1.2.1 = w.1 at h
    omega⟩
  invFun k := ⟨(take w k, drop w k), append_take_drop w k⟩
  left_inv := by
    rintro ⟨⟨u, v⟩, h⟩
    apply Subtype.ext
    apply Prod.ext
    · change take w u.1 = u
      rw [← h, take_append]
    · change drop w u.1 = v
      rw [← h, drop_append]
  right_inv k := by
    apply Fin.ext
    change (take w k).1 = k
    rw [length_take, min_eq_left (Nat.le_of_lt_succ k.2)]

@[simp] lemma appendFiberEquiv_apply (w : Word ι) (p : appendFiber w) :
    (appendFiberEquiv w p : ℕ) = p.1.1.1 := rfl

@[simp] lemma appendFiberEquiv_symm_apply (w : Word ι) (k : Fin (w.1 + 1)) :
    ((appendFiberEquiv w).symm k).1 = (take w k, drop w k) := rfl

noncomputable instance instFintypeAppendFiber (w : Word ι) : Fintype (appendFiber w) :=
  Fintype.ofEquiv _ (appendFiberEquiv w).symm

/-- There are exactly one more splits than letters, including the two endpoint splits. -/
lemma card_appendFiber (w : Word ι) : Fintype.card (appendFiber w) = w.1 + 1 := by
  rw [Fintype.card_congr (appendFiberEquiv w), Fintype.card_fin]

/-- Every fiber of concatenation is finite, even over an infinite alphabet. -/
lemma finite_append_preimage_singleton (w : Word ι) :
    ((fun p : Word ι × Word ι ↦ append p.1 p.2) ⁻¹' {w}).Finite := by
  change Set.Finite {p : Word ι × Word ι | append p.1 p.2 = w}
  exact Set.finite_def.mpr ⟨instFintypeAppendFiber w⟩

lemma ncard_append_preimage_singleton (w : Word ι) :
    ((fun p : Word ι × Word ι ↦ append p.1 p.2) ⁻¹' {w}).ncard = w.1 + 1 := by
  change Nat.card (appendFiber w) = w.1 + 1
  rw [Nat.card_eq_fintype_card, card_appendFiber]

/-- Every decomposition is the prefix/suffix split at its first word's length. -/
lemma append_eq_iff (u v w : Word ι) :
    append u v = w ↔ ∃ k : Fin (w.1 + 1), u = take w k ∧ v = drop w k := by
  constructor
  · intro h
    refine ⟨appendFiberEquiv w ⟨(u, v), h⟩, ?_, ?_⟩
    · change u = take w u.1
      rw [← h, take_append]
    · change v = drop w u.1
      rw [← h, drop_append]
  · rintro ⟨k, rfl, rfl⟩
    exact append_take_drop w k

end PoissonWord
