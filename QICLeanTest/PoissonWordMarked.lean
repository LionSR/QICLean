/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordMarked

/-! Regression consumers for positions, endpoint insertions, and degenerate alphabets. -/

open PoissonWord

namespace PoissonWordMarkedTest

-- An infinite alphabet needs no enumeration or finiteness hypothesis.
example : (Σ w : Word ℕ, Fin w.1) ≃ Word ℕ × ℕ × Word ℕ := markedWordEquiv

-- Inserting at either endpoint recovers precisely the empty prefix or suffix.
example {ι : Type*} (a : ι) (v : Word ι) :
    markedWordEquiv (markedInsert nil a v) = (nil, a, v) :=
  markedWordEquiv.apply_symm_apply (nil, a, v)

example {ι : Type*} (u : Word ι) (a : ι) :
    markedWordEquiv (markedInsert u a nil) = (u, a, nil) :=
  markedWordEquiv.apply_symm_apply (u, a, nil)

-- The inserted letter lies between the prefix and suffix in their original order.
example : List.ofFn (insert (singleton false) true (singleton false)).2 =
    [false, true, false] := by
  simp only [ofFn_insert, ofFn_singleton, List.singleton_append]

-- Equal letters at different positions remain different marked words.
example : markedWordEquiv (⟨⟨2, fun _ ↦ ()⟩, 0⟩ : MarkedWord Unit) ≠
    markedWordEquiv (⟨⟨2, fun _ ↦ ()⟩, 1⟩ : MarkedWord Unit) := by
  intro h
  have hpos := congrArg (fun p : MarkedWord Unit ↦ (p.2 : ℕ))
    (markedWordEquiv.injective h)
  exact Nat.zero_ne_one hpos

-- Every inverse records its actual insertion position and total length.
example {ι : Type*} (u : Word ι) (a : ι) (v : Word ι) :
    ((markedWordEquiv.symm (u, a, v)).2 : ℕ) = u.1 ∧
      (markedWordEquiv.symm (u, a, v)).1.1 = u.1 + v.1 + 1 := by
  simp

-- An empty alphabet has no marked word, even though its empty word exists.
example {ι : Type*} [IsEmpty ι] : IsEmpty (MarkedWord ι) :=
  ⟨fun p ↦ isEmptyElim (p.1.2 p.2)⟩

example (p : MarkedWord (Fin 0)) : False := Fin.elim0 (p.1.2 p.2)

-- The inverse retains the original mark, not just the unmarked word.
example {ι : Type*} (w : Word ι) (j : Fin w.1) :
    markedInsert (take w j) (w.2 j) (drop w (j + 1)) = ⟨w, j⟩ :=
  markedWordEquiv.symm_apply_apply ⟨w, j⟩

end PoissonWordMarkedTest
