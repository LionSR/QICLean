/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SurprisalMoment

/-!
# Typical sets of a surprisal distribution

For a probability vector `p`, a center `S` and a width `w`, the typical set consists of
the indices with `p_i > 0` and `|-log p_i - S| ≤ w`. Its mass `z` is at least one minus
the tail probability `Pr {|K - S| > w}`, and its members have weights between
`e^{-S-w}` and `e^{-S+w}`.

## Main results

* `Entropy.one_sub_surprisalTail_le_typicalMass`: the typical mass bound.
* `Entropy.exp_le_of_mem_typicalSet`: the weight bounds on the typical set.

## References

* Two-dimensional area-law manuscript (September 24, 2026), the concentration statement
  after Lemma 3.1, `02-initial.tex`, lines 209–219, and the typical Schmidt data of
  Proposition 8.1, `07-comparators.tex`, lines 17–64.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators

namespace Entropy

variable {ι : Type*} [Fintype ι]

/-- The typical set: positive weights whose surprisal lies within `w` of `S`. -/
noncomputable def typicalSet (p : ι → ℝ) (S w : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ 0 < p i ∧ |-Real.log (p i) - S| ≤ w

/-- The mass of the typical set. -/
noncomputable def typicalMass (p : ι → ℝ) (S w : ℝ) : ℝ := ∑ i ∈ typicalSet p S w, p i

theorem mem_typicalSet {p : ι → ℝ} {S w : ℝ} {i : ι} :
    i ∈ typicalSet p S w ↔ 0 < p i ∧ |-Real.log (p i) - S| ≤ w := by
  classical
  simp [typicalSet]

/-- The typical mass is at least one minus the tail probability. -/
theorem one_sub_surprisalTail_le_typicalMass {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (S w : ℝ) : 1 - surprisalTail p S w ≤ typicalMass p S w := by
  classical
  have h : ∑ i, p i ≤ typicalMass p S w + surprisalTail p S w := by
    rw [typicalMass, surprisalTail, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ typicalSet p S w) p]
    gcongr ?_ + ?_
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    · calc ∑ i ∈ Finset.univ.filter (· ∉ typicalSet p S w), p i
          = ∑ i ∈ Finset.univ.filter (· ∉ typicalSet p S w),
              (if w < |-Real.log (p i) - S| then p i else 0) := by
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [Finset.mem_filter, mem_typicalSet] at hi
            split_ifs with h
            · rfl
            · rcases (hp i).eq_or_lt with h0 | h0
              · rw [← h0]
              · exact absurd ⟨h0, not_lt.mp h⟩ hi.2
        _ ≤ ∑ i, (if w < |-Real.log (p i) - S| then p i else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ Finset.univ)
              fun i _ _ ↦ by split_ifs <;> simp [hp i]
  linarith

theorem typicalMass_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (S w : ℝ) :
    0 ≤ typicalMass p S w :=
  Finset.sum_nonneg fun i _ ↦ hp i

theorem typicalMass_le_one {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (S w : ℝ) :
    typicalMass p S w ≤ 1 :=
  hs ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hp i

/-- Members of the typical set have weights between `e^{-S-w}` and `e^{-S+w}`, the form
of the typical Schmidt data used by the normalized-restriction estimates. -/
theorem exp_le_of_mem_typicalSet {p : ι → ℝ} {S w : ℝ} {i : ι} (hi : i ∈ typicalSet p S w) :
    Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w) := by
  rw [mem_typicalSet] at hi
  have h := abs_le.mp hi.2
  rw [← Real.exp_log hi.1]
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

end Entropy
