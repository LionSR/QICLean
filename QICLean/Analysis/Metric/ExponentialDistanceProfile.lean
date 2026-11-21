/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Exponential profiles of distance to a set

The profile is `exp (-a * d(y, S)^α)` at finite extended distance and zero at
infinite extended distance. The triangle inequality and subadditivity of the
power for `0 < α ≤ 1` turn a weighted row bound into a kernel supersolution.
In particular, the empty set and components at infinite distance retain
literal zero profiles.

This proves the metric step in `09-amplification.tex`, lines 159–188, without
assuming a profile transfer inequality or an evolution estimate.
-/

open scoped BigOperators ENNReal

namespace Real

/-- The scalar exponential comparison following from subadditivity of a
power of exponent at most one. -/
lemma exp_neg_mul_rpow_le_of_le_add {a α x d z : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hx : 0 ≤ x) (hd : 0 ≤ d) (hz : 0 ≤ z) (hxdz : x ≤ d + z) :
    exp (-a * z ^ α) ≤ exp (a * d ^ α) * exp (-a * x ^ α) := by
  have hpow : x ^ α ≤ d ^ α + z ^ α :=
    (rpow_le_rpow hx hxdz hα).trans (rpow_add_le_add_rpow hd hz hα hα₁)
  rw [← exp_add]
  apply exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hpow ha]

end Real

namespace Metric

variable {κ : Type*} [PseudoEMetricSpace κ]

/-- Exponential decay away from a set, with value zero at infinite distance. -/
noncomputable def exponentialDistanceProfile (S : Set κ) (a α : ℝ) (y : κ) : ℝ := by
  classical
  exact if infEDist y S = ∞ then 0 else Real.exp (-a * (infEDist y S).toReal ^ α)

lemma exponentialDistanceProfile_nonneg (S : Set κ) (a α : ℝ) (y : κ) :
    0 ≤ exponentialDistanceProfile S a α y := by
  unfold exponentialDistanceProfile
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

@[simp]
lemma exponentialDistanceProfile_eq_zero_iff (S : Set κ) (a α : ℝ) (y : κ) :
    exponentialDistanceProfile S a α y = 0 ↔ infEDist y S = ∞ := by
  classical
  unfold exponentialDistanceProfile
  split_ifs with h
  · simp [h]
  · simp [h, Real.exp_ne_zero]

lemma exponentialDistanceProfile_of_ne_top (S : Set κ) (a α : ℝ) (y : κ)
    (hy : infEDist y S ≠ ∞) :
    exponentialDistanceProfile S a α y = Real.exp (-a * (infEDist y S).toReal ^ α) := by
  simp [exponentialDistanceProfile, hy]

lemma exponentialDistanceProfile_eq_one_of_mem {S : Set κ} (a : ℝ) {α : ℝ}
    (hα : 0 < α) {y : κ} (hy : y ∈ S) :
    exponentialDistanceProfile S a α y = 1 := by
  simp [exponentialDistanceProfile, infEDist_zero_of_mem hy, Real.zero_rpow hα.ne']

/-- The distance profile dominates the literal indicator of the target set. -/
lemma indicator_one_le_exponentialDistanceProfile (S : Set κ) (a : ℝ) {α : ℝ}
    (hα : 0 < α) (y : κ) :
    S.indicator (fun _ ↦ (1 : ℝ)) y ≤ exponentialDistanceProfile S a α y := by
  classical
  by_cases hy : y ∈ S
  · simp [hy, exponentialDistanceProfile_eq_one_of_mem a hα hy]
  · simpa [hy] using exponentialDistanceProfile_nonneg S a α y

@[simp]
lemma exponentialDistanceProfile_empty (a α : ℝ) (y : κ) :
    exponentialDistanceProfile ∅ a α y = 0 := by
  simp [exponentialDistanceProfile]

/-- A finite pair distance transfers the decay profile by its exponential
weight. The infinite-distance branch is settled before taking real values. -/
lemma exponentialDistanceProfile_le_exp_mul (S : Set κ) {a α : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1) {y z : κ}
    (hyz : edist y z ≠ ∞) :
    exponentialDistanceProfile S a α z ≤
      Real.exp (a * (edist y z).toReal ^ α) * exponentialDistanceProfile S a α y := by
  by_cases hz : infEDist z S = ∞
  · rw [(exponentialDistanceProfile_eq_zero_iff S a α z).2 hz]
    exact mul_nonneg (Real.exp_pos _).le (exponentialDistanceProfile_nonneg S a α y)
  · have htriangle : infEDist y S ≤ edist y z + infEDist z S :=
      infEDist_le_edist_add_infEDist
    have hy : infEDist y S ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hyz, hz⟩) htriangle
    rw [exponentialDistanceProfile_of_ne_top S a α z hz,
      exponentialDistanceProfile_of_ne_top S a α y hy]
    exact Real.exp_neg_mul_rpow_le_of_le_add ha hα.le hα₁
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (ENNReal.toReal_le_add htriangle hyz hz)

/-- A nonnegative kernel with no entries across infinite distance and a
weighted full-row bound has the exponential distance profile as a
supersolution. No finiteness assumption on the distance to the set is needed. -/
theorem sum_mul_exponentialDistanceProfile_le [Fintype κ]
    (S : Set κ) (A : κ → κ → ℝ) {a α v : ℝ}
    (ha : 0 ≤ a) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hA : ∀ y z, 0 ≤ A y z)
    (hsupport : ∀ y z, edist y z = ∞ → A y z = 0)
    (hrow : ∀ y, (∑ z : κ, A y z * Real.exp (a * (edist y z).toReal ^ α)) ≤ v)
    (y : κ) :
    (∑ z : κ, A y z * exponentialDistanceProfile S a α z) ≤
      v * exponentialDistanceProfile S a α y := by
  calc
    _ ≤ ∑ z : κ, (A y z * Real.exp (a * (edist y z).toReal ^ α)) *
        exponentialDistanceProfile S a α y := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hyz : edist y z = ∞
      · simp [hsupport y z hyz]
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (exponentialDistanceProfile_le_exp_mul S ha hα hα₁ hyz) (hA y z)
    _ = (∑ z : κ, A y z * Real.exp (a * (edist y z).toReal ^ α)) *
        exponentialDistanceProfile S a α y := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow y)
      (exponentialDistanceProfile_nonneg S a α y)

end Metric
