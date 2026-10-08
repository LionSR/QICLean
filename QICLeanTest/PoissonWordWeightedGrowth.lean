/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordWeightedGrowth

/-! Alphabet-rate normalization, unbounded observables, and zero-profile regressions. -/

open MeasureTheory PoissonWord
open scoped BigOperators NNReal

namespace PoissonWordWeightedGrowthTest

-- There are two rate-one labels: the exponential rate is two, not one.
-- The observable 2^length is unbounded over all words.
example (T : ℝ≥0) :
    Integrable (fun u : Word (Fin 2) ↦ (2 : ℝ) ^ u.1) (measure (Fin 2) T) ∧
      (∫ u : Word (Fin 2), (2 : ℝ) ^ u.1 ∂measure (Fin 2) T) ≤
        Real.exp (2 * T) := by
  have h := integrable_and_integral_le_of_weighted_growth T
    (fun u : Word (Fin 2) ↦ fun _ : Unit ↦ (2 : ℝ) ^ u.1)
    (fun _ _ : Unit ↦ (2 : ℝ)) (fun _ : Unit ↦ (1 : ℝ))
    (v := 2) (C := 1) (fun _ _ ↦ by positivity)
    (fun _ _ ↦ by norm_num) (fun _ ↦ by norm_num) (by norm_num) (by norm_num)
    (fun _ ↦ by simp [nil])
    (by
      intro u y
      simp only [length_append, length_singleton, pow_succ, Fin.sum_univ_two,
        Fintype.sum_unique]
      ring_nf
      exact le_rfl)
    (fun _ ↦ by simp) ()
  simpa using h

-- No labels means no increments, and the time bound is constant.
example (T : ℝ≥0) (f : Word (Fin 0) → ℝ) {C : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hC : 0 ≤ C) (h0 : f nil ≤ C) :
    Integrable f (measure (Fin 0) T) ∧ (∫ u, f u ∂measure (Fin 0) T) ≤ C := by
  have h := integrable_and_integral_le_of_weighted_growth T
    (fun u : Word (Fin 0) ↦ fun _ : Unit ↦ f u)
    (fun _ _ : Unit ↦ (0 : ℝ)) (fun _ : Unit ↦ (1 : ℝ))
    (v := 0) (C := C) (fun u _ ↦ hf u)
    (fun _ _ ↦ le_rfl) (fun _ ↦ zero_le_one) le_rfl hC
    (fun _ ↦ by simpa using h0) (fun _ _ ↦ by simp) (fun _ ↦ by simp) ()
  simpa using h

-- A zero row profile propagates exact vanishing at every word, not just almost surely.
example {ι : Type*} [Fintype ι]
    (f : Word ι → Bool → ℝ) (A : Bool → Bool → ℝ) {v C : ℝ}
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hv : 0 ≤ v) (hC : 0 ≤ C)
    (h0 : ∀ y, f nil y ≤ C * (if y then 0 else 1))
    (hs : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : Bool, A y z * f u z)
    (hAr : ∀ y, (∑ z : Bool, A y z * (if z then 0 else 1)) ≤
      v * (if y then 0 else 1)) (u : Word ι) : f u true = 0 :=
  eq_zero_of_weighted_growth_of_profile_eq_zero f A (fun y ↦ if y then 0 else 1)
    hf hA hv hC h0 hs hAr true (by simp) u

-- With a zero kernel, a nonpositive total increment cannot increase expectation.
example {ι : Type*} [Fintype ι] (T : ℝ≥0) (f : Word ι → ℝ) {C : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hC : 0 ≤ C) (h0 : f nil ≤ C)
    (hs : ∀ u, (∑ i : ι, (f (append u (singleton i)) - f u)) ≤ 0) :
    Integrable f (measure ι T) ∧ (∫ u, f u ∂measure ι T) ≤ C := by
  have h := integrable_and_integral_le_of_weighted_growth T
    (fun u ↦ fun _ : Unit ↦ f u) (fun _ _ : Unit ↦ (0 : ℝ))
    (fun _ : Unit ↦ (1 : ℝ)) (v := 0) (C := C)
    (fun u _ ↦ hf u) (fun _ _ ↦ le_rfl) (fun _ ↦ zero_le_one) le_rfl hC
    (fun _ ↦ by simpa using h0) (fun u _ ↦ by simpa using hs u)
    (fun _ ↦ by simp) ()
  simpa using h

end PoissonWordWeightedGrowthTest
