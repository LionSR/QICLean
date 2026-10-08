/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordAppend

/-! Chronological order, empty increments, and three-increment association. -/

open Matrix PoissonWord
open scoped MatrixOrder ComplexOrder

variable {n ι : Type*} [Fintype n] [DecidableEq n]

-- Two specified event labels have the later square-root factor on the left.
example (k : ι → Matrix n n ℂ) (i j : ι) :
    contractionWord k (append (⟨1, fun _ => i⟩ : Word ι) ⟨1, fun _ => j⟩).1
      (append (⟨1, fun _ => i⟩ : Word ι) ⟨1, fun _ => j⟩).2 =
      CFC.sqrt (1 - k j) * CFC.sqrt (1 - k i) := by
  rw [contractionWord_word_append]
  simp [contractionWord]

-- Either empty increment has identity action.
example (k : ι → Matrix n n ℂ) (w : Word ι) :
    contractionWord k (append nil w).1 (append nil w).2 =
      contractionWord k w.1 w.2 := by
  rw [contractionWord_word_append]
  simp [nil]

example (k : ι → Matrix n n ℂ) (w : Word ι) :
    contractionWord k (append w nil).1 (append w nil).2 =
      contractionWord k w.1 w.2 := by
  rw [contractionWord_word_append]
  simp [nil]

-- Three successive increments preserve their chronological nesting.
example (k : ι → Matrix n n ℂ) (u v w : Word ι) :
    contractionWord k (append (append u v) w).1 (append (append u v) w).2 =
      contractionWord k w.1 w.2 *
        (contractionWord k v.1 v.2 * contractionWord k u.1 u.2) := by
  rw [contractionWord_word_append, contractionWord_word_append]
