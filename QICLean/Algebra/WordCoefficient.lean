/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.WordMultiplicity
import Mathlib.Data.List.OfFn

/-!
# Actual ordered-word coefficients

The coefficient of a prescribed frequency vector is the sum of all ordered products
with those letter counts. Renaming the alphabet bijectively preserves the counts.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--617.
-/

open scoped BigOperators

namespace WordMultiplicity

/-- The actual ordered-word coefficient for a prescribed full frequency vector.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 604--617. -/
noncomputable def wordCoefficient {ι R : Type*} [Fintype ι] [Semiring R]
    (H : ι → R) (degree : ℕ) (α : ι → ℕ) : R :=
  open Classical in
  ∑ w ∈ (Finset.univ : Finset (Fin degree → ι)).filter
      (fun w ↦ (countsFinsupp w : ι → ℕ) = α),
    (List.ofFn (fun p ↦ H (w p))).prod

/-- Counts are preserved when the alphabet is renamed bijectively.
AKLV, arXiv:1301.1162v1, the word-frequency expansion in Lemma 4.2. -/
theorem countsFinsupp_equiv {ι κ : Type*} (e : ι ≃ κ) {degree : ℕ}
    (w : Fin degree → ι) (a : ι) :
    countsFinsupp (fun p ↦ e (w p)) (e a) = countsFinsupp w a := by
  classical
  simp only [countsFinsupp, Finsupp.finsetSum_apply, Finsupp.single_apply,
    e.injective.eq_iff]

end WordMultiplicity
