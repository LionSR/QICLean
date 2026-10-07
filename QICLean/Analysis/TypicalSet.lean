/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SurprisalMoment
import Mathlib.Algebra.BigOperators.Field

/-!
# Typical sets of a surprisal distribution

For a probability vector `p`, a center `S` and a width `w`, the typical set consists of
the indices with `p_i > 0` and `|-log p_i - S| ≤ w`. Its mass `z` is at least one minus
the tail probability `Pr {|K - S| > w}`. On the typical set, the normalized weights
`p_i / z` satisfy `|log |E| - S| ≤ w + |log z|` and `|S' - S| ≤ w + |log z|`, where `S'`
is their entropy.

## Main results

* `Entropy.one_sub_surprisalTail_le_typicalMass`: the typical mass bound.
* `Entropy.abs_log_card_typicalSet_sub_le`: the cardinality of the typical set.
* `Entropy.abs_typicalEntropy_sub_le`: the entropy of the normalized typical weights.

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

/-- The entropy of the normalized typical weights `p_i / z`. -/
noncomputable def typicalEntropy (p : ι → ℝ) (S w : ℝ) : ℝ :=
  ∑ i ∈ typicalSet p S w, Real.negMulLog (p i / typicalMass p S w)

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

/-- On the typical set, the normalized surprisal `-log (p_i / z)` lies within
`w + |log z|` of `S`. -/
private theorem abs_neg_log_div_sub_le {p : ι → ℝ} {S w : ℝ} {i : ι}
    (hi : i ∈ typicalSet p S w) (hz : 0 < typicalMass p S w)
    (hz1 : typicalMass p S w ≤ 1) :
    |-Real.log (p i / typicalMass p S w) - S| ≤ w + |Real.log (typicalMass p S w)| := by
  rw [mem_typicalSet] at hi
  rw [Real.log_div hi.1.ne' hz.ne']
  have h1 := abs_le.mp hi.2
  have hl : Real.log (typicalMass p S w) ≤ 0 := Real.log_nonpos hz.le hz1
  rw [abs_of_nonpos hl, abs_le]
  constructor <;> linarith

/-- **Cardinality of the typical set.** If the typical mass `z` is positive, then
`|log |E| - S| ≤ w + |log z|`.
Area-law manuscript, `07-comparators.tex`, lines 17–64, the typical Schmidt data. -/
theorem abs_log_card_typicalSet_sub_le {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {S w : ℝ} (hz : 0 < typicalMass p S w) :
    |Real.log (typicalSet p S w).card - S| ≤ w + |Real.log (typicalMass p S w)| := by
  set z := typicalMass p S w
  set E := typicalSet p S w
  have hz1 := typicalMass_le_one hp hs S w
  set c := w + |Real.log z|
  have hE : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [z, typicalMass, E, h] at hz
  have hcard : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  -- each normalized weight lies in `[e^{-(S + c)}, e^{-(S - c)}]`
  have hbounds (i : ι) (hi : i ∈ E) :
      Real.exp (-(S + c)) ≤ p i / z ∧ p i / z ≤ Real.exp (-(S - c)) := by
    have h := abs_le.mp (abs_neg_log_div_sub_le hi hz hz1)
    have hpos : 0 < p i / z := div_pos (mem_typicalSet.mp hi).1 hz
    constructor
    · rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr (by linarith)
    · rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr (by linarith)
  have hsum : ∑ i ∈ E, p i / z = 1 := by rw [← Finset.sum_div]; exact div_self hz.ne'
  have hlow : E.card * Real.exp (-(S + c)) ≤ 1 := by
    rw [← hsum, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi ↦ (hbounds i hi).1
  have hupp : 1 ≤ E.card * Real.exp (-(S - c)) := by
    rw [← hsum, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi ↦ (hbounds i hi).2
  have h1 : Real.log E.card - (S + c) ≤ 0 := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at this
    linarith
  have h2 : 0 ≤ Real.log E.card - (S - c) := by
    have := Real.log_le_log one_pos hupp
    rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at this
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Entropy of the normalized typical weights.** If the typical mass `z` is positive,
the entropy `S'` of `p_i / z` on the typical set satisfies `|S' - S| ≤ w + |log z|`.
Area-law manuscript, `07-comparators.tex`, lines 17–64, the typical Schmidt data. -/
theorem abs_typicalEntropy_sub_le {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {S w : ℝ} (hz : 0 < typicalMass p S w) :
    |typicalEntropy p S w - S| ≤ w + |Real.log (typicalMass p S w)| := by
  set z := typicalMass p S w
  set E := typicalSet p S w
  have hz1 := typicalMass_le_one hp hs S w
  have hsum : ∑ i ∈ E, p i / z = 1 := by rw [← Finset.sum_div]; exact div_self hz.ne'
  have hrw : typicalEntropy p S w - S = ∑ i ∈ E, p i / z * (-Real.log (p i / z) - S) := by
    simp only [typicalEntropy, Real.negMulLog, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hsum, one_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hrw]
  calc |∑ i ∈ E, p i / z * (-Real.log (p i / z) - S)|
      ≤ ∑ i ∈ E, |p i / z * (-Real.log (p i / z) - S)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ E, p i / z * (w + |Real.log z|) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [abs_mul, abs_of_nonneg (div_nonneg (hp i) hz.le)]
        exact mul_le_mul_of_nonneg_left (abs_neg_log_div_sub_le hi hz hz1)
          (div_nonneg (hp i) hz.le)
    _ = w + |Real.log z| := by rw [← Finset.sum_mul, hsum, one_mul]

end Entropy
