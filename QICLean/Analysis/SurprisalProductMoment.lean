/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SurprisalMoment
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact surprisal moments of independent copies

The moment of a finite product law is the corresponding power of the
one-copy moment. Zero weights contribute zero before logarithms are
expanded. The identity also holds for zero copies and does not require
normalization of the weights.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 218--238,
`comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace Entropy

/-- Independent finite copies have multiplicative surprisal moments.
The weights may vanish and need not sum to one. Source:
`07-comparators.tex`, lines 218--238. -/
theorem surprisalMoment_pi {n : Type*} [Fintype n]
    (p : n → ℝ) (k : ℕ) (u : ℝ) :
    surprisalMoment (fun x : Fin k → n ↦ ∏ j, p (x j)) u =
      surprisalMoment p u ^ k := by
  unfold surprisalMoment
  trans ∑ x : Fin k → n, ∏ j, p (x j) * Real.exp (u * -Real.log (p (x j)))
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    done
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Fintype.prod_sum (fun (_ : Fin k) i ↦ p i * Real.exp (u * -Real.log (p i)))).symm

end Entropy
