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
each coefficient to one pair of indices and their occurrence counts. The
same finite set of bins works for every degree up to a prescribed cutoff.

Source: AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–625;
ALVV, arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1323–1326.

The common-cutoff proof is adapted from
`TNLean/MPS/AreaLaw/TwoWindowPolynomialRank.lean` at TNLean commit
`3f0017131d2a8ba3321e737874684b88d616a7a1`, without changing its argument.
The exact-degree theorem is now its specialization at equal degree and cutoff.
-/

open scoped BigOperators

open Classical in
/-- A common pair of local frequency selectors partitions every degree up to
a prescribed bound into the same finite set of bins.
ALVV, arXiv:1602.08828v2, `prop:Cheby-AGSP-eff`, lines 1324–1332;
AKLV, arXiv:1301.1162v1, Lemma `l:agsp`, lines 604–625. -/
theorem Fintype.exists_two_window_word_coefficient_partition_of_le
    {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡]
    (L R : Finset ι) (hL : L.Nonempty) (hR : R.Nonempty) :
    ∃ pickL : (↥L → ℕ) → ↥L,
      ∃ pickR : (↥R → ℕ) → ↥R,
        (∀ (f : ι → ℕ) (k : ℕ), (∑ a, f a) ≤ k →
          f (pickL (fun u : ↥L ↦ f u)) ≤ k / L.card ∧
          f (pickR (fun v : ↥R ↦ f v)) ≤ k / R.card) ∧
        ∀ (H : ι → 𝓡) (k r : ℕ), r ≤ k →
          let A := Finset.piAntidiag (Finset.univ : Finset ι) r
          let B := (L.product (Finset.range (k / L.card + 1))).product
            (R.product (Finset.range (k / R.card + 1)))
          let left : (ι → ℕ) → ↥L := fun α ↦ pickL (fun u : ↥L ↦ α u)
          let right : (ι → ℕ) → ↥R := fun α ↦ pickR (fun v : ↥R ↦ α v)
          let label : (ι → ℕ) → (ι × ℕ) × (ι × ℕ) := fun α ↦
            (((left α : ι), α (left α)), ((right α : ι), α (right α)))
          let coefficient : (ι → ℕ) → 𝓡 := fun α ↦
            ∑ w ∈ (Finset.univ : Finset (Fin r → ι)).filter
                (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = α),
              (List.ofFn (fun t ↦ H (w t))).prod
          (∑ x, H x) ^ r =
            ∑ t ∈ B, ∑ α ∈ A with label α = t, coefficient α := by
  obtain ⟨pickL, pickR, hpick⟩ :=
    Finset.exists_two_window_low_frequency_selectors L R hL hR
  refine ⟨pickL, pickR, hpick, ?_⟩
  intro H k r hr A B left right label coefficient
  have hword : ∀ w ∈ (Finset.univ : Finset (Fin r → ι)),
      (WordMultiplicity.countsFinsupp w : ι → ℕ) ∈ A :=
    fun w _ ↦ Finset.mem_piAntidiag.mpr
      ⟨WordMultiplicity.sum_counts w, fun _ _ ↦ Finset.mem_univ _⟩
  have hcoeff : (∑ x, H x) ^ r = ∑ α ∈ A, coefficient α :=
    (Fintype.sum_pow_eq_sum_ordered_words H r).trans
      (Finset.sum_fiberwise_of_maps_to hword
        (fun w ↦ (List.ofFn (fun t ↦ H (w t))).prod)).symm
  refine hcoeff.trans (Finset.sum_fiberwise_of_maps_to ?_ coefficient).symm
  intro α hα
  obtain ⟨hleft, hright⟩ := hpick α k ((Finset.mem_piAntidiag.mp hα).1.le.trans hr)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr
      ⟨(left α).property, Finset.mem_range.mpr (Nat.lt_succ_of_le hleft)⟩,
      Finset.mem_product.mpr
        ⟨(right α).property, Finset.mem_range.mpr (Nat.lt_succ_of_le hright)⟩⟩

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
  obtain ⟨pickL, pickR, hpick, hpartition⟩ :=
    Fintype.exists_two_window_word_coefficient_partition_of_le (𝓡 := 𝓡) L R hL hR
  exact ⟨pickL, pickR, hpick, fun H k ↦ hpartition H k k (le_refl k)⟩
