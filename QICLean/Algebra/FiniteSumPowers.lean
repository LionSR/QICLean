/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Ordered words in a power of a finite sum

A power of a finite sum is the sum of its ordered words. The identity
holds in an arbitrary semiring and does not require commuting summands.
It includes the empty alphabet and exponent zero.

This is the word expansion used in LVV, arXiv:1307.5143v1, equation
eq:a-exp, lines 606–609, and AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 604–617. The spectral normalization of the power approximation and
the collection of words with prescribed multiplicities are separate results.
-/

open scoped BigOperators

/-- Ordered expansion of a power of a finite sum. LVV, arXiv:1307.5143v1,
equation eq:a-exp, lines 606–609; AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 604–617. -/
theorem Fintype.sum_pow_eq_sum_ordered_words
    {ι R : Type*} [Fintype ι] [Semiring R] (P : ι → R) (m : ℕ) :
    (∑ i, P i) ^ m =
      ∑ w : Fin m → ι, (List.ofFn (fun j => P (w j))).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    rw [← Fintype.sum_prod_type (fun p : ι × (Fin m → ι) =>
      P p.1 * (List.ofFn (fun j => P (p.2 j))).prod)]
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => ι)) _ _ ?_
    simp [Fin.consEquiv, List.ofFn_succ]
