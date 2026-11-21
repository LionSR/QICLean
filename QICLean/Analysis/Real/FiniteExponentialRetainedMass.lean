/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum

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

section ExponentialPolynomialAbsorption

/-!
# Exponential errors below inverse polynomial mass

An exponentially decreasing error is eventually smaller than the retained
Schur-label mass, including the shift in the copy number. This scalar fact
does not assert any concentration estimate for a state.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–354,
  `comparator:rough-overlap`.

-/

open Filter Topology

namespace Real

/-- Every fixed real multiple of a decreasing exponential is eventually below
one quarter of the shifted inverse polynomial. In the retained-mass argument
the multiple is the number of imposed cutoffs. The conclusion includes zero
multiple and zero polynomial degree. -/
theorem eventually_mul_exp_neg_le_inv_four_pow_add_one
    {c : ℝ} (hc : 0 < c) (m : ℝ) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      m * exp (-c * (k : ℝ)) ≤ 1 / (4 * (((k + 1 : ℕ) : ℝ) ^ d)) := by
  have hshift : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto
      (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ d *
        exp (-c * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) c hc).comp hshift
  have hscaled : Tendsto
      (fun k : ℕ ↦ (4 * m * exp c) *
        (((k + 1 : ℕ) : ℝ) ^ d * exp (-c * ((k + 1 : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hdecay.const_mul (4 * m * exp c)
  filter_upwards [hscaled.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hk
  have hfactor : exp c * exp (-c * ((k + 1 : ℕ) : ℝ)) =
      exp (-c * (k : ℝ)) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((k + 1 : ℕ) : ℝ) ^ d)).2
  calc
    (m * exp (-c * (k : ℝ))) * (4 * ((k + 1 : ℕ) : ℝ) ^ d) =
        (4 * m * exp c) *
          (((k + 1 : ℕ) : ℝ) ^ d * exp (-c * ((k + 1 : ℕ) : ℝ))) := by
      rw [← hfactor]
      ring
    _ ≤ 1 := hk.le

end Real

end ExponentialPolynomialAbsorption

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

section FiveMomentExponentialBound

/-!
# A common mass in five exponential moment bounds

A common nonnegative mass appears once after taking the product of five
fifth moments. The zero-mass case is included, without logarithms of that
mass or normalization of the underlying positive measure.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 520--560,
`comparator:merge-moments` and `comparator:component-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace Real

/-- Five nonnegative moments with a common exponential bound retain the
common mass once in their geometric mean. Source: `07-comparators.tex`,
lines 520--560. The common mass may vanish. -/
theorem prod_five_rpow_le_common_exp
    (M A : Fin 5 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ i, 0 ≤ M i) (hbound : ∀ i, M i ≤ c * exp (A i)) :
    (∏ i, M i ^ (1 / 5 : ℝ)) ≤ c * exp ((∑ i, A i) / 5) := by
  calc
    (∏ i, M i ^ (1 / 5 : ℝ)) ≤
        ∏ i, c ^ (1 / 5 : ℝ) * exp (A i * (1 / 5 : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact rpow_nonneg (hM i) _
      · intro i _
        simpa only [mul_rpow hc (exp_pos (A i)).le, ← exp_mul] using
          rpow_le_rpow (hM i) (hbound i) (by norm_num : (0 : ℝ) ≤ 1 / 5)
    _ = (c ^ (1 / 5 : ℝ)) ^ 5 * exp ((∑ i, A i) * (1 / 5 : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← exp_sum, ← Finset.sum_mul]
    _ = c * exp ((∑ i, A i) / 5) := by
      rw [← rpow_mul_natCast hc]
      norm_num [div_eq_mul_inv]

end Real

end FiveMomentExponentialBound
