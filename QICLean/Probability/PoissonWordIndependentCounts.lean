/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordCounts
import Mathlib.Probability.Independence.Basic

/-!
# Independent Poisson counts of a finite random word

The count vector of the actual atomic Poissonized-word measure has the product
of Poisson laws of rate `t`. The proof sums equal word masses over the finite
multinomial fiber, then compares singleton masses on the countable count space.
Independence and the individual count laws are conclusions of this calculation.

This is the fixed-time count characterization in the amplification source,
`09-amplification.tex`, lines 49–54 and 237–253. It does not construct event
times, independent increments, or an identification of sample paths.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal Nat

namespace PoissonWord

variable {ι : Type*} [Fintype ι]

/-- The mass of a prescribed count event is the number of compatible words
multiplied by their common singleton mass. -/
lemma measure_countEvent (t : ℝ≥0) (n : ι → ℕ) :
    measure ι t (countEvent n) = (Fintype.card (countFiber n) : ℝ≥0∞) *
      ENNReal.ofReal (weight ι t (∑ i, n i)) := by
  classical
  have hsum : (∑' w : countFiber n, measure ι t {w.1}) =
      measure ι t (countEvent n) := by
    simpa using tsum_measure_preimage_singleton (μ := measure ι t)
      (s := countEvent n) (f := id) (Set.to_countable _)
      (fun w _ ↦ measurableSet_singleton w)
  rw [← hsum, tsum_fintype]
  have hlength (w : countFiber n) : w.1.1 = ∑ i, n i := by
    rw [← sum_countVector w.1, show countVector w.1 = n from w.2]
  simp_rw [measure_singleton, hlength]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Multinomial counting cancels the factorial in the common word weight. -/
lemma card_countFiber_mul_weight (t : ℝ≥0) (n : ι → ℕ) :
    (Fintype.card (countFiber n) : ℝ) * weight ι t (∑ i, n i) =
      ∏ i, (Real.exp (-(t : ℝ)) * (t : ℝ) ^ n i / ((n i)! : ℝ)) := by
  classical
  have hfactorial : (∏ i, ((n i)! : ℝ)) * (Fintype.card (countFiber n) : ℝ) =
      ((∑ i, n i)! : ℝ) := by
    rw [card_countFiber]
    exact_mod_cast Nat.multinomial_spec Finset.univ n
  have hprod : (∏ i, ((n i)! : ℝ)) ≠ 0 := by positivity
  have htotal : ((∑ i, n i)! : ℝ) ≠ 0 := by positivity
  rw [weight, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul,
    Finset.prod_pow_eq_pow_sum]
  simp only [mul_neg, neg_mul]
  apply (eq_div_iff hprod).2
  calc
    _ = (Real.exp (-((Fintype.card ι : ℝ) * t)) * (t : ℝ) ^ (∑ i, n i)) *
        ((∏ i, ((n i)! : ℝ)) * (Fintype.card (countFiber n) : ℝ) /
          ((∑ i, n i)! : ℝ)) := by ring
    _ = _ := by rw [hfactorial, div_self htotal, mul_one]

/-- The count-event mass is the product of the one-dimensional Poisson masses. -/
lemma measure_countEvent_eq_prod (t : ℝ≥0) (n : ι → ℕ) :
    measure ι t (countEvent n) =
      ∏ i, ProbabilityTheory.poissonMeasure t {n i} := by
  classical
  simp_rw [ProbabilityTheory.poissonMeasure_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ by positivity),
    measure_countEvent, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_countFiber_mul_weight]

/-- The actual count vector has the product Poisson law, including at time zero
and for an empty alphabet. Source: amplification, lines 49–54 and 237–253. -/
theorem map_countVector (t : ℝ≥0) :
    (measure ι t).map countVector =
      Measure.pi (fun _ : ι ↦ ProbabilityTheory.poissonMeasure t) := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton n),
    Measure.pi_singleton]
  exact measure_countEvent_eq_prod t n

/-- Every label count has Poisson law of rate `t`. -/
lemma map_countVector_apply (t : ℝ≥0) (i : ι) :
    (measure ι t).map (fun w ↦ countVector w i) =
      ProbabilityTheory.poissonMeasure t := by
  change (measure ι t).map (Function.eval i ∘ countVector) = _
  rw [← Measure.map_map (measurable_pi_apply i) Measurable.of_discrete,
    map_countVector]
  exact (measurePreserving_eval (fun _ : ι ↦ ProbabilityTheory.poissonMeasure t) i).map_eq

/-- Counts of distinct labels are mutually independent under the word measure. -/
theorem iIndepFun_countVector (t : ℝ≥0) :
    ProbabilityTheory.iIndepFun (fun i w ↦ countVector w i) (measure ι t) := by
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun _ ↦ Measurable.of_discrete.aemeasurable)).2
  simpa only [map_countVector_apply] using map_countVector (ι := ι) t

end PoissonWord
