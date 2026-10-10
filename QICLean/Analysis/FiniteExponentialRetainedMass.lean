/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ExponentialPolynomialAbsorption
import Mathlib.Order.Filter.Finite

/-!
# Finite exponential losses below a retained polynomial mass

A fixed finite sum of exponentially decreasing errors is eventually smaller
than one quarter of the prescribed inverse polynomial. Consequently, a
projection whose initial squared norm is at least one half of that inverse
polynomial retains at least half its mass after such losses.

These are scalar estimates. For the area-law application, the individual
errors are derived from the actual regional marginals and the initial mass
comes from the previously selected auxiliary Schur label.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 338–354,
  `comparator:rough-overlap`, manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Filter Topology
open scoped BigOperators

namespace Real

variable {I : Type*} [Fintype I]

/-- Finitely many positive exponential rates can be absorbed into the same
shifted inverse polynomial. The rates need not be equal. -/
theorem eventually_sum_exp_neg_le_inv_four_pow_add_one
    (c : I → ℝ) (hc : ∀ i, 0 < c i) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (∑ i, exp (-c i * (k : ℝ))) ≤
        1 / (4 * (((k + 1 : ℕ) : ℝ) ^ d)) := by
  classical
  by_cases hI : Nonempty I
  · let := hI
    have hm : 0 < (Fintype.card I : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have h := eventually_all.mpr fun i ↦
      eventually_mul_exp_neg_le_inv_four_pow_add_one (hc i) (Fintype.card I : ℝ) d
    filter_upwards [h] with k hk
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hk i)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsum
    exact (mul_le_mul_iff_right₀ hm).mp hsum
  · have : IsEmpty I := not_nonempty_iff.mp hI
    filter_upwards [] with k
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity

/-- An eventual inverse-polynomial lower bound on the selected mass survives
finitely many exponentially small losses. The same original mass is retained;
no second selection is made. This scalar lemma is used after the actual
projection inequality and actual regional tail estimates have been proved. -/
theorem eventually_half_mass_of_exponential_losses
    (q r : ℕ → ℝ) (loss : I → ℕ → ℝ) (d : ℕ)
    (hmass : ∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ d)) ≤ q k)
    (hretain : ∀ k, q k - ∑ i, loss i k ≤ r k)
    (htail : ∀ i, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in atTop, loss i k ≤ exp (-c * (k : ℝ))) :
    ∀ᶠ k : ℕ in atTop,
      q k / 2 ≤ r k ∧ 1 / (4 * (((k + 1 : ℕ) : ℝ) ^ d)) ≤ r k := by
  classical
  choose c hc htail using htail
  have hsum := eventually_sum_exp_neg_le_inv_four_pow_add_one c hc d
  have hall := eventually_all.mpr htail
  filter_upwards [hmass, hsum, hall] with k hmass hsum htail
  have hloss : (∑ i, loss i k) ≤ 1 / (4 * (((k + 1 : ℕ) : ℝ) ^ d)) :=
    (Finset.sum_le_sum fun i _ ↦ htail i).trans hsum
  have hp : 0 < (((k + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hhalf : 1 / (2 * (((k + 1 : ℕ) : ℝ) ^ d)) =
      2 * (1 / (4 * (((k + 1 : ℕ) : ℝ) ^ d))) := by
    field_simp [hp.ne']
    ring
  rw [hhalf] at hmass
  have hret := hretain k
  constructor <;> linarith

end Real
