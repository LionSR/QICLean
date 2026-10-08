/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecay
import QICLean.Probability.PoissonWordAppend

/-!
# Chronological products under word concatenation

The factors from the later word act on the left. This algebraic identity
connects the append law of finite words with chronological square-root products;
it requires no commutation, positivity, spectral gap, or clock process.
-/

namespace Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- Appending a later tuple multiplies its chronological product on the left. -/
theorem contractionWord_append (k : ι → Matrix n n ℂ) {a b : ℕ}
    (u : Fin a → ι) (v : Fin b → ι) :
    contractionWord k (a + b) (Fin.append u v) =
      contractionWord k b v * contractionWord k a u := by
  induction v using Fin.snocInduction with
  | elim0 => simp
  | @snoc b v i ih =>
    rw [Fin.append_snoc]
    change contractionWord k ((a + b) + 1) (Fin.snoc (Fin.append u v) i) =
      contractionWord k (b + 1) (Fin.snoc v i) * contractionWord k a u
    rw [contractionWord_snoc, contractionWord_snoc, ih, mul_assoc]

/-- The literal word append map has the same latest-factor-on-the-left convention. -/
theorem contractionWord_word_append (k : ι → Matrix n n ℂ) (u v : PoissonWord.Word ι) :
    contractionWord k (PoissonWord.append u v).1 (PoissonWord.append u v).2 =
      contractionWord k v.1 v.2 * contractionWord k u.1 u.2 :=
  contractionWord_append k u.2 v.2

end Matrix
