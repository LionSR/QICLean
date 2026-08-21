/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixFittingRange
import QICLean.Kraus.WordSpan

/-!
# Bounded word powers in a finite Kraus family

This file constructs a bounded-length word-span element whose range lies in the
sum of the generalized eigenspaces for nonzero eigenvalues. It gives only the
intermediate Fitting-projector-power step $A_1^r = A_1^r P$ in Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347, Lemma 2(b), not the final
rank-one element $|\varphi\rangle\langle\psi|$.
-/

open scoped Matrix
open Module

namespace Kraus

variable {d D : ℕ}

/-- A power of an evaluated word belongs to the word span at the multiplied length. -/
theorem evalWord_pow_mem_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)) (k : ℕ) :
    (Kraus.evalWord K w) ^ k ∈ wordSpan K (k * w.length) := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hw : Kraus.evalWord K w ∈ wordSpan K w.length :=
        evalWord_mem_wordSpan K w
      have hprod :
          (Kraus.evalWord K w) ^ k * Kraus.evalWord K w ∈
            wordSpan K (k * w.length + w.length) := by
        rw [wordSpan_add]
        exact Submodule.mul_mem_mul ih hw
      simpa [pow_succ, Nat.succ_mul] using hprod

end Kraus
