/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Basic

/-!
# Local choices of low-frequency indices

For two nonempty finite subsets of a finite alphabet, choose an index in each
as a function of its local natural frequencies. The two choice functions are
fixed before the global frequency function and its total bound. The selected
frequencies are at most that bound divided by the respective subset sizes.
The subsets may overlap, and the total frequency may be zero.

This is the elementary selection step in the simultaneous frequency argument.
No operator decomposition, interpolation, rank estimate or spectral assertion
is part of this result.

Source: AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 619–625;
ALVV, arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1323–1326.
-/

open scoped BigOperators

open Classical in
private noncomputable def natWindowMinimum
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ↥s → ℕ) : ↥s :=
  Classical.choose (Finset.exists_min_image s.attach f hs.attach)

open Classical in
/-- Choose indices using only the frequencies within each window.

AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 619–625; ALVV,
arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1323–1326. The choices
precede the global frequency function and its upper bound. The windows need
not be disjoint. This is an auxiliary selection result, not the full rank or
spectral-projector theorem.
-/
theorem Finset.exists_two_window_low_frequency_selectors
    {ι : Type*} [Fintype ι]
    (L R : Finset ι) (hL : L.Nonempty) (hR : R.Nonempty) :
    ∃ pickL : (↥L → ℕ) → ↥L,
      ∃ pickR : (↥R → ℕ) → ↥R,
        ∀ (f : ι → ℕ) (k : ℕ), (∑ a, f a) ≤ k →
          f (pickL (fun u : ↥L ↦ f u)) ≤ k / L.card ∧
          f (pickR (fun v : ↥R ↦ f v)) ≤ k / R.card := by
  refine ⟨natWindowMinimum L hL, natWindowMinimum R hR, ?_⟩
  suffices hwindow : ∀ (s : Finset ι) (hs : s.Nonempty) (f : ι → ℕ) (k : ℕ),
      (∑ a, f a) ≤ k →
        f (natWindowMinimum s hs (fun u : ↥s ↦ f u)) ≤ k / s.card by
    intro f k hsum
    exact ⟨hwindow L hL f k hsum, hwindow R hR f k hsum⟩
  intro s hs f k hsum
  have hmul : s.card * f (natWindowMinimum s hs (fun u : ↥s ↦ f u)) ≤
      ∑ a ∈ s, f a := by
    calc
      _ = ∑ _a ∈ s, f (natWindowMinimum s hs (fun u : ↥s ↦ f u)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun a ha ↦
        (Classical.choose_spec (Finset.exists_min_image s.attach
          (fun u : ↥s ↦ f u) hs.attach)).2 ⟨a, ha⟩ (s.mem_attach _)
  have hsub : (∑ a ∈ s, f a) ≤ ∑ a, f a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ ↦ Nat.zero_le _)
  exact (Nat.le_div_iff_mul_le hs.card_pos).2
    ((Nat.mul_comm _ _).trans_le (hmul.trans (hsub.trans hsum)))
