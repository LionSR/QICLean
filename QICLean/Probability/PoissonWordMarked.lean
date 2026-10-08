/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordAppend

/-!
# Finite words with a marked letter

A word with a chosen position is equivalent to its prefix, the letter at that
position, and its suffix. The inverse inserts the letter and marks the position
immediately after the prefix. Positions remain distinct when letters repeat,
and no finiteness assumption on the alphabet is needed.
-/

namespace PoissonWord

variable {ι : Type*}

/-- A word containing exactly one letter. -/
def singleton (a : ι) : Word ι := ⟨1, fun _ ↦ a⟩

@[simp] lemma length_singleton (a : ι) : (singleton a).1 = 1 := rfl

@[simp] lemma ofFn_singleton (a : ι) : List.ofFn (singleton a).2 = [a] := by
  simp [singleton, List.ofFn_succ]

/-- Insert a letter between a specified prefix and suffix. -/
def insert (u : Word ι) (a : ι) (v : Word ι) : Word ι :=
  append u (append (singleton a) v)

@[simp] lemma length_insert (u : Word ι) (a : ι) (v : Word ι) :
    (insert u a v).1 = u.1 + v.1 + 1 := by
  simp only [insert, length_append, length_singleton]
  omega

@[simp] lemma ofFn_insert (u : Word ι) (a : ι) (v : Word ι) :
    List.ofFn (insert u a v).2 = List.ofFn u.2 ++ a :: List.ofFn v.2 := by
  simp only [insert, append, List.ofFn_fin_append, ofFn_singleton, List.singleton_append]

@[simp] lemma take_insert (u : Word ι) (a : ι) (v : Word ι) :
    take (insert u a v) u.1 = u :=
  take_append u (append (singleton a) v)

@[simp] lemma drop_insert (u : Word ι) (a : ι) (v : Word ι) :
    drop (insert u a v) (u.1 + 1) = v := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (drop (insert u a v) (u.1 + 1)).2 = List.ofFn v.2
  simp only [ofFn_drop, ofFn_insert, List.drop_append, List.length_ofFn]
  simp

/-- Removing a marked letter and then inserting it recovers the word. -/
@[simp] lemma insert_take_get_drop (w : Word ι) (j : Fin w.1) :
    insert (take w j) (w.2 j) (drop w (j + 1)) = w := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (insert (take w j) (w.2 j) (drop w (j + 1))).2 = List.ofFn w.2
  simp only [ofFn_insert, ofFn_take, ofFn_drop]
  have hj : (j : ℕ) < (List.ofFn w.2).length := by simp
  have h := List.take_append_drop (j : ℕ) (List.ofFn w.2)
  rw [List.drop_eq_getElem_cons hj] at h
  simpa only [List.getElem_ofFn] using h

/-- A finite word together with the position of one of its letters. -/
abbrev MarkedWord (ι : Type*) := Σ w : Word ι, Fin w.1

/-- Insert a letter and retain its position immediately after the prefix. -/
def markedInsert (u : Word ι) (a : ι) (v : Word ι) : MarkedWord ι :=
  ⟨insert u a v, ⟨u.1, by rw [length_insert]; omega⟩⟩

@[simp] lemma markedInsert_word (u : Word ι) (a : ι) (v : Word ι) :
    (markedInsert u a v).1 = insert u a v := rfl

@[simp] lemma markedInsert_position (u : Word ι) (a : ι) (v : Word ι) :
    ((markedInsert u a v).2 : ℕ) = u.1 := rfl

@[simp] lemma markedInsert_letter (u : Word ι) (a : ι) (v : Word ι) :
    (markedInsert u a v).1.2 (markedInsert u a v).2 = a := by
  have h : u.1 < (List.ofFn (insert u a v).2).length := by
    simp only [List.length_ofFn, length_insert]
    omega
  have heq : (List.ofFn (insert u a v).2)[u.1] = a := by
    simp only [ofFn_insert, List.getElem_append, List.length_ofFn, Nat.lt_irrefl,
      ↓reduceDIte, Nat.sub_self, List.getElem_cons_zero]
  simpa only [List.getElem_ofFn, markedInsert] using heq

/-- Splitting at the chosen position is a bijection with prefix-letter-suffix triples. -/
def markedWordEquiv : MarkedWord ι ≃ Word ι × ι × Word ι where
  toFun p := (take p.1 p.2, p.1.2 p.2, drop p.1 (p.2 + 1))
  invFun p := markedInsert p.1 p.2.1 p.2.2
  left_inv p := by
    apply Sigma.ext (insert_take_get_drop p.1 p.2)
    apply (Fin.heq_ext_iff (congrArg Sigma.fst (insert_take_get_drop p.1 p.2))).2
    exact length_take_of_le p.1 (Nat.le_of_lt p.2.2)
  right_inv := by
    rintro ⟨u, a, v⟩
    exact Prod.ext (take_insert u a v)
      (Prod.ext (markedInsert_letter u a v) (drop_insert u a v))

@[simp] lemma markedWordEquiv_apply (p : MarkedWord ι) :
    markedWordEquiv p = (take p.1 p.2, p.1.2 p.2, drop p.1 (p.2 + 1)) := rfl

@[simp] lemma markedWordEquiv_symm_apply (u : Word ι) (a : ι) (v : Word ι) :
    markedWordEquiv.symm (u, a, v) = markedInsert u a v := rfl

end PoissonWord
