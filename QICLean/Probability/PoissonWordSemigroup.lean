/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordAppend
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Time composition of Poissonized finite words

Concatenating independent word samples with durations `s` and `t` gives the word
law with duration `s + t`. The proof sums over the actual prefix/suffix decompositions of
each word and evaluates their scalar weights by the binomial theorem.

This is a time-composition property of the explicit word measures used in the
amplification source, `09-amplification.tex`, lines 49–54. It does not construct
event times, a process with independent increments, or a coupling of paths.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal Nat

namespace PoissonWord

variable {ι : Type*} [Fintype ι]

/-- The convolution of word weights over all possible split lengths is the
word weight at the sum of the two times. -/
lemma sum_weight_mul_weight (s t : ℝ≥0) (m : ℕ) :
    (∑ k : Fin (m + 1), weight ι s k * weight ι t (m - k)) =
      weight ι (s + t) m := by
  have hterm (k : Fin (m + 1)) :
      weight ι s k * weight ι t (m - k) =
        (Real.exp (-(Fintype.card ι : ℝ) * ((s : ℝ) + t)) / (m ! : ℝ)) *
          ((s : ℝ) ^ (k : ℕ) * (t : ℝ) ^ (m - k) * (m.choose k : ℝ)) := by
    have hfactorial : (m.choose k : ℝ) * ((k : ℕ)! : ℝ) * ((m - k)! : ℝ) =
        (m ! : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ k.2)
    have hk : ((k : ℕ)! : ℝ) ≠ 0 := by positivity
    have hr : ((m - k)! : ℝ) ≠ 0 := by positivity
    have hm : (m ! : ℝ) ≠ 0 := by positivity
    simp only [weight, mul_add, Real.exp_add]
    field_simp [hk, hr, hm]
    rw [← hfactorial]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun k ↦ (s : ℝ) ^ k * (t : ℝ) ^ (m - k) * (m.choose k : ℝ)), ← add_pow]
  simp only [weight, NNReal.coe_add]
  ring

/-- The product measure of the actual concatenation fiber has the singleton
mass of the word law at the combined time. -/
lemma prod_measure_append_preimage_singleton (s t : ℝ≥0) (w : Word ι) :
    ((measure ι s).prod (measure ι t))
        ((fun p : Word ι × Word ι ↦ append p.1 p.2) ⁻¹' {w}) =
      ENNReal.ofReal (weight ι (s + t) w.1) := by
  classical
  have hsum : (∑ p : appendFiber w, ((measure ι s).prod (measure ι t)) {p.1}) =
      ((measure ι s).prod (measure ι t))
        ((fun p : Word ι × Word ι ↦ append p.1 p.2) ⁻¹' {w}) := by
    have h : (∑' p : appendFiber w, ((measure ι s).prod (measure ι t)) {p.1}) =
        ((measure ι s).prod (measure ι t))
          ((fun p : Word ι × Word ι ↦ append p.1 p.2) ⁻¹' {w}) :=
      tsum_measure_preimage_singleton
      (μ := (measure ι s).prod (measure ι t))
      (s := (fun p : Word ι × Word ι ↦ append p.1 p.2) ⁻¹' {w}) (f := id)
      (finite_append_preimage_singleton w).countable
      (fun p _ ↦ measurableSet_singleton p)
    simpa only [tsum_fintype] using h
  rw [← hsum, ← (appendFiberEquiv w).symm.sum_comp
    (fun p : appendFiber w ↦ ((measure ι s).prod (measure ι t)) {p.1})]
  have htake (k : Fin (w.1 + 1)) : (take w k).1 = k :=
    length_take_of_le w (Nat.le_of_lt_succ k.2)
  simp_rw [appendFiberEquiv_symm_apply, ← Set.singleton_prod_singleton,
    Measure.prod_prod, measure_singleton, htake, length_drop,
    ← ENNReal.ofReal_mul (weight_nonneg s _)]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun (k : Fin (w.1 + 1)) _ ↦
      mul_nonneg (weight_nonneg (ι := ι) s k) (weight_nonneg t (w.1 - k))),
    sum_weight_mul_weight]

/-- Independent word samples with two durations concatenate to the word law at the
sum of the times, including zero times and an empty alphabet. -/
theorem map_append (s t : ℝ≥0) :
    ((measure ι s).prod (measure ι t)).map
        (fun p : Word ι × Word ι ↦ append p.1 p.2) =
      measure ι (s + t) := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton w),
    measure_singleton]
  exact prod_measure_append_preimage_singleton s t w

end PoissonWord
