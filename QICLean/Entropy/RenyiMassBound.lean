/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.MeanInequalities

/-!
# Rényi entropy and concentration on a finite set

For order greater than one, a set carrying mass at least `1 - δ` must have
large cardinality if the Rényi entropy is large. All logarithms are natural.

Source: Schuch, Wolf, Verstraete and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 333–345. The displayed lower bound in the source has an
incorrect plus sign before the absolute logarithm; the preceding power-sum
inequality gives the minus sign proved here.

**Local fix (error-term sign):** the correction is documented in TNLean's
[Rényi bond-dimension sign note](https://github.com/LionSR/TNLean/commit/ebf04b6495d29691ddefac5c85dd70ca6ba3bad6#diff-83cdf7e9f9eb1a229f1f7c212c73baa355968807efb4cef898c364519490b75a).
-/

open scoped BigOperators

namespace Entropy

/-- A finite set carrying mass at least `1 - δ` has the cardinality required by
the Rényi power sum of order `α > 1`. Normalization of the entire family is
unnecessary. Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
lines 333–345, with the corrected sign of the error term. -/
theorem log_card_bound_of_renyi_mass {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset ι) {D : ℕ}
    (hD : 0 < D) (hcard : s.card ≤ D) {α δ : ℝ} (hα : 1 < α)
    (hδ : δ < 1) (hmass : 1 - δ ≤ ∑ i ∈ s, p i) :
    Real.log (∑ i, p i ^ α) / (1 - α) +
      α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  have ha : 0 < α := lt_trans zero_lt_one hα
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have ht : 0 < 1 - δ := sub_pos.mpr hδ
  have hj := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := p) hα.le
    (fun i _ ↦ hp i)
  have hpow : (1 - δ) ^ α ≤ (D : ℝ) ^ (α - 1) * ∑ i, p i ^ α := by
    refine (Real.rpow_le_rpow ht.le hmass ha.le).trans (hj.trans ?_)
    apply mul_le_mul
    · exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcard)
        (sub_nonneg.mpr hα.le)
    · exact Finset.sum_le_univ_sum_of_nonneg (fun i ↦ Real.rpow_nonneg (hp i) α)
    · exact Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (hp i) α)
    · positivity
  have hsum : 0 < ∑ i, p i ^ α := by
    have hprod : 0 < (D : ℝ) ^ (α - 1) * ∑ i, p i ^ α :=
      (Real.rpow_pos_of_pos ht α).trans_le hpow
    exact pos_of_mul_pos_right hprod (Real.rpow_nonneg hd.le _)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos ht α) hpow
  rw [Real.log_rpow ht, Real.log_mul (by positivity) hsum.ne',
    Real.log_rpow hd] at hlog
  rw [show 1 - α = -(α - 1) by ring, div_neg, div_mul_eq_mul_div, ← neg_div,
    ← add_div]
  apply (div_le_iff₀ (sub_pos.mpr hα)).mpr
  linarith

/-- The corrected absolute-logarithm form of the Rényi cardinality bound.
Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 333–345. -/
theorem renyi_mass_sub_error_le_log_card {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset ι) {D : ℕ}
    (hD : 0 < D) (hcard : s.card ≤ D) {α δ : ℝ} (hα : 1 < α)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hmass : 1 - δ ≤ ∑ i ∈ s, p i) :
    Real.log (∑ i, p i ^ α) / (1 - α) -
      α / (α - 1) * |Real.log (1 - δ)| ≤ Real.log D := by
  have hlog : Real.log (1 - δ) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr hδ1).le (by linarith)
  simpa only [abs_of_nonpos hlog, mul_neg, sub_neg_eq_add] using
    log_card_bound_of_renyi_mass p hp s hD hcard hα hδ1 hmass

end Entropy
