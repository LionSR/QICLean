/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordAppend

/-! Consumers of concatenation and its finite fibers, including degenerate alphabets. -/

open PoissonWord

namespace PoissonWordAppendTest

-- An infinite alphabet still gives a finite fiber with exactly one split per position.
example (w : Word ℕ) : Fintype.card (appendFiber w) = w.1 + 1 := card_appendFiber w

example (w : Word ℕ) :
    ((fun p : Word ℕ × Word ℕ ↦ append p.1 p.2) ⁻¹' {w}).Finite :=
  finite_append_preimage_singleton w

-- Repeated letters do not collapse distinct split positions.
example : Fintype.card (appendFiber (⟨3, fun _ ↦ ()⟩ : Word Unit)) = 4 :=
  card_appendFiber _

-- The empty alphabet has one decomposition of its empty word.
example : Fintype.card (appendFiber (nil : Word (Fin 0))) = 1 := card_appendFiber _

-- The equivalence constructs the actual prefix and suffix, with the required lengths.
example (w : Word ℕ) (k : Fin (w.1 + 1)) :
    (((appendFiberEquiv w).symm k).1.1.1,
      ((appendFiberEquiv w).symm k).1.2.1) = ((k : ℕ), w.1 - k) := by
  simp only [appendFiberEquiv_symm_apply, length_drop,
    length_take_of_le w (Nat.le_of_lt_succ k.2)]

-- Appending preserves the order of distinct letters.
example : append (⟨1, fun _ ↦ false⟩ : Word Bool) ⟨1, fun _ ↦ true⟩ ≠
    append (⟨1, fun _ ↦ true⟩ : Word Bool) ⟨1, fun _ ↦ false⟩ := by
  intro h
  have hlist := congrArg (fun w : Word Bool ↦ List.ofFn w.2) h
  simp only [append, List.ofFn_fin_append] at hlist
  simp [List.ofFn_succ] at hlist

-- Empty words remain genuine two-sided identities for every alphabet.
example {ι : Type*} (w : Word ι) : append nil w = w ∧ append w nil = w := by simp

example {ι : Type*} (u v w : Word ι) :
    append (append u v) w = append u (append v w) := append_assoc u v w

end PoissonWordAppendTest
