/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.LowFrequencySelection
import QICLean.Algebra.FiniteSumPowers
import QICLean.Algebra.WordMultiplicity
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

/-!
# A common partition of ordered-word coefficients

The full-frequency coefficients are sums of ordered words in a finite
operator family. Two choices made from local frequency restrictions assign
each coefficient to one pair of indices and their occurrence counts.

Source: AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–625;
ALVV, arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1323–1326.
-/

open scoped BigOperators

open Classical in
/-- Partition the actual full-frequency coefficients by one common pair of
selected indices and their frequencies. This is an auxiliary algebraic step
in AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–625, and ALVV,
arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1323–1326.
-/
theorem Fintype.exists_two_window_word_coefficient_partition
    {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡]
    (L R : Finset ι) (hL : L.Nonempty) (hR : R.Nonempty) :
    ∃ pickL : (↥L → ℕ) → ↥L,
      ∃ pickR : (↥R → ℕ) → ↥R,
        (∀ (f : ι → ℕ) (k : ℕ), (∑ a, f a) ≤ k →
          f (pickL (fun u : ↥L ↦ f u)) ≤ k / L.card ∧
          f (pickR (fun v : ↥R ↦ f v)) ≤ k / R.card) ∧
        ∀ (H : ι → 𝓡) (k : ℕ),
          let E := Finset.piAntidiag (Finset.univ : Finset ι) k
          let B := (L.product (Finset.range (k / L.card + 1))).product
            (R.product (Finset.range (k / R.card + 1)))
          let left : (ι → ℕ) → ↥L := fun a ↦ pickL (fun u : ↥L ↦ a u)
          let right : (ι → ℕ) → ↥R := fun a ↦ pickR (fun v : ↥R ↦ a v)
          let label : (ι → ℕ) → (ι × ℕ) × (ι × ℕ) := fun a ↦
            (((left a : ι), a (left a)), ((right a : ι), a (right a)))
          let coefficient : (ι → ℕ) → 𝓡 := fun a ↦
            ∑ w ∈ (Finset.univ : Finset (Fin k → ι)).filter
                (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
              (List.ofFn (fun p ↦ H (w p))).prod
          (∑ x, H x) ^ k =
            ∑ t ∈ B, ∑ a ∈ E with label a = t, coefficient a := by
  classical
  obtain ⟨pickL, pickR, hpick⟩ :=
    Finset.exists_two_window_low_frequency_selectors L R hL hR
  refine ⟨pickL, pickR, hpick, ?_⟩
  intro H k E B left right label coefficient
  have hword : ∀ w ∈ (Finset.univ : Finset (Fin k → ι)),
      (WordMultiplicity.countsFinsupp w : ι → ℕ) ∈ E := by
    intro w _
    exact Finset.mem_piAntidiag.mpr
      ⟨WordMultiplicity.sum_counts w, fun _ _ ↦ Finset.mem_univ _⟩
  have hcoeff : (∑ x, H x) ^ k = ∑ a ∈ E, coefficient a := by
    rw [Fintype.sum_pow_eq_sum_ordered_words]
    exact (Finset.sum_fiberwise_of_maps_to hword
      (fun w ↦ (List.ofFn (fun p ↦ H (w p))).prod)).symm
  apply hcoeff.trans
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro a ha
  have hsum : (∑ x, a x) = k := (Finset.mem_piAntidiag.mp ha).1
  obtain ⟨hleft, hright⟩ := hpick a k hsum.le
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr
      ⟨(left a).property, Finset.mem_range.mpr (Nat.lt_succ_of_le hleft)⟩,
      Finset.mem_product.mpr
        ⟨(right a).property, Finset.mem_range.mpr (Nat.lt_succ_of_le hright)⟩⟩
