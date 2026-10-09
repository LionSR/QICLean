/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ExponentialDistanceProfile

/-! Infinite-distance branches, empty targets, and the exponent-zero boundary. -/

open scoped BigOperators ENNReal

namespace ExponentialDistanceProfileTest

private def separatedDistance (x y : Bool) : ℝ≥0∞ := if x = y then 0 else ∞

private noncomputable abbrev separatedSpace : PseudoEMetricSpace Bool :=
  PseudoEMetricSpace.ofEDist separatedDistance
    (fun x ↦ by simp [separatedDistance])
    (fun x y ↦ by simp [separatedDistance, eq_comm])
    (fun x y z ↦ by cases x <;> cases y <;> cases z <;> simp [separatedDistance])

-- The second site is in a different component; toReal infinity must not erase that.
example :
    letI := separatedSpace
    Metric.exponentialDistanceProfile {false} 1 1 false = 1 ∧
      Metric.exponentialDistanceProfile {false} 1 1 true = 0 := by
  let _ := separatedSpace
  constructor
  · exact Metric.exponentialDistanceProfile_eq_one_of_mem 1 (by norm_num) (by simp)
  · apply (Metric.exponentialDistanceProfile_eq_zero_iff _ _ _ _).2
    rw [Metric.infEDist_singleton]
    rfl

-- Empty targets stay zero even when the decay parameter is zero.
example {κ : Type*} [PseudoEMetricSpace κ] (y : κ) :
    Metric.exponentialDistanceProfile ∅ 0 1 y = 0 := by simp

-- At exponent zero the intended normalization on the target fails: 0^0 = 1.
example :
    letI := separatedSpace
    Metric.exponentialDistanceProfile {false} 1 0 false = Real.exp (-1) ∧
      Metric.exponentialDistanceProfile {false} 1 0 false < 1 := by
  let _ := separatedSpace
  have h : Metric.exponentialDistanceProfile {false} 1 0 false = Real.exp (-1) := by
    simp [Metric.exponentialDistanceProfile, Metric.infEDist_zero_of_mem
      (by simp : false ∈ ({false} : Set Bool))]
  exact ⟨h, h ▸ Real.exp_lt_one_iff.mpr (by norm_num)⟩

-- The no-cross-component kernel hypothesis is essential, even with a weighted row bound.
example :
    letI := separatedSpace
    let A : Bool → Bool → ℝ := fun y z ↦ if y = true ∧ z = false then 1 else 0
    (∑ z : Bool, A true z * Metric.exponentialDistanceProfile {false} 0 1 z) = 1 ∧
      Metric.exponentialDistanceProfile {false} 0 1 true = 0 ∧
      ∀ y, (∑ z : Bool, A y z * Real.exp (0 * (edist y z).toReal ^ (1 : ℝ))) ≤ 1 := by
  let _ := separatedSpace
  have hfalse : Metric.exponentialDistanceProfile {false} 0 1 false = 1 :=
    Metric.exponentialDistanceProfile_eq_one_of_mem 0 (by norm_num) (by simp)
  have htrue : Metric.exponentialDistanceProfile {false} 0 1 true = 0 := by
    apply (Metric.exponentialDistanceProfile_eq_zero_iff _ _ _ _).2
    rw [Metric.infEDist_singleton]
    rfl
  refine ⟨?_, htrue, ?_⟩
  · simp [hfalse]
  · intro y
    cases y <;> norm_num

-- The scalar comparison includes alpha=1 and an exactly saturated triangle inequality.
example (a d z : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hz : 0 ≤ z) :
    Real.exp (-a * z) ≤ Real.exp (a * d) * Real.exp (-a * (d + z)) := by
  simpa using Real.exp_neg_mul_rpow_le_of_le_add ha (by norm_num : (0 : ℝ) ≤ 1)
    le_rfl (add_nonneg hd hz) hd hz le_rfl

end ExponentialDistanceProfileTest
