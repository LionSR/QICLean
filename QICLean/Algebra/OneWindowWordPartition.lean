/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.LowFrequencySelection
import QICLean.Algebra.FiniteSumPowers
import QICLean.Algebra.WordCoefficient
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Fintype.Pi

/-!
# One-window partition of the actual ordered-word coefficients

A selector depending only on the occurrence counts within a nonempty window is chosen
before the operator family, degree and degree cutoff. It partitions every power into
bins indexed by a selected interaction and its low frequency. The coefficients are
sums of actual ordered words, including all multiplicities.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--625.
No coefficient-rank estimate or suitable distinguished interaction is assumed.
-/

open scoped BigOperators

open Classical in
/-- A common local selector partitions every power up to a prescribed degree into actual
low-frequency bins. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 604--625. -/
theorem Fintype.exists_one_window_word_coefficient_partition_of_le
    {ι R : Type*} [Fintype ι] [Semiring R] (S : Finset ι) (hS : S.Nonempty) :
    ∃ pick : (S → ℕ) → S,
      (∀ (f : ι → ℕ) (ell : ℕ), (∑ a, f a) ≤ ell →
        f (pick (fun u : S ↦ f u)) ≤ ell / S.card) ∧
      ∀ (H : ι → R) (ell degree : ℕ), degree ≤ ell →
        let E := Finset.piAntidiag (Finset.univ : Finset ι) degree
        let B := S.product (Finset.range (ell / S.card + 1))
        let chosen : (ι → ℕ) → S := fun α ↦ pick (fun u : S ↦ α u)
        let label : (ι → ℕ) → ι × ℕ := fun α ↦ (chosen α, α (chosen α))
        let coefficient := WordMultiplicity.wordCoefficient H degree
        (∑ a, H a) ^ degree =
          ∑ b ∈ B, ∑ α ∈ E with label α = b, coefficient α := by
  obtain ⟨pick, _, hpick⟩ := Finset.exists_two_window_low_frequency_selectors S S hS hS
  refine ⟨pick, fun f ell hsum ↦ (hpick f ell hsum).1, ?_⟩
  intro H ell degree hdegree E B chosen label coefficient
  have hword : ∀ w ∈ (Finset.univ : Finset (Fin degree → ι)),
      (WordMultiplicity.countsFinsupp w : ι → ℕ) ∈ E :=
    fun w _ ↦ Finset.mem_piAntidiag.mpr
      ⟨WordMultiplicity.sum_counts w, fun _ _ ↦ Finset.mem_univ _⟩
  have hcoeff : (∑ a, H a) ^ degree = ∑ α ∈ E, coefficient α :=
    (Fintype.sum_pow_eq_sum_ordered_words H degree).trans
      (Finset.sum_fiberwise_of_maps_to hword
        (fun w ↦ (List.ofFn (fun p ↦ H (w p))).prod)).symm
  refine hcoeff.trans (Finset.sum_fiberwise_of_maps_to ?_ coefficient).symm
  intro α hα
  have hlow := (hpick α ell ((Finset.mem_piAntidiag.mp hα).1.le.trans hdegree)).1
  exact Finset.mem_product.mpr
    ⟨(chosen α).property, Finset.mem_range.mpr (Nat.lt_succ_of_le hlow)⟩
