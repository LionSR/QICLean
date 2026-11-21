/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite capped geometric sums

A geometric tail capped by one has total mass bounded by a logarithmic initial
cost and a geometric remainder. This is the scalar summation used to correct
the general approximate-projector entropy estimate in AKLV, arXiv:1301.1162v1,
Lemma 2.3 (`lem:S`), lines 339–348. No assertion about an operator is made here.
-/

open scoped BigOperators

namespace Real

/-- The finite geometric sum is bounded uniformly by its positive denominator. -/
private theorem finite_geometric_sum_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (M : ℕ) : (∑ i ∈ Finset.range M, δ ^ i) ≤ 1 / (1 - δ) := by
  apply (le_div_iff₀ (sub_pos.mpr hδ1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hδ0 M)

/-- The geometric remainder has the scale of the inverse logarithmic decay. -/
private theorem inv_one_sub_le_log {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 / (1 - δ) ≤ 1 + 1 / (-log δ) := by
  have hx : 0 < -log δ := neg_pos.mpr (log_neg hδ0 hδ1)
  have h := log_le_sub_one_of_pos (inv_pos.mpr hδ0)
  rw [log_inv] at h
  have hh : δ * (-log δ) ≤ 1 - δ := by
    have hm := mul_le_mul_of_nonneg_left h hδ0.le
    rw [mul_sub, mul_inv_cancel₀ hδ0.ne', mul_one] at hm
    exact hm
  apply (div_le_iff₀ (sub_pos.mpr hδ1)).2
  have hratio : δ ≤ (1 - δ) / (-log δ) := (le_div_iff₀ hx).2 hh
  calc
    1 = (1 - δ) + δ := by ring
    _ ≤ (1 - δ) + (1 - δ) / (-log δ) := add_le_add le_rfl hratio
    _ = (1 + 1 / (-log δ)) * (1 - δ) := by ring

/-- Finite capped geometric mass has logarithmic dependence on its amplitude.
This quantitative scalar bound supports the corrected estimate for AKLV,
arXiv:1301.1162v1, Lemma 2.3 (`lem:S`), lines 339–348. -/
theorem sum_min_one_mul_pow_le (A δ : ℝ) (hA : 0 ≤ A)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (M : ℕ) :
    (∑ i ∈ Finset.range M, min 1 (A * δ ^ i)) ≤
      2 + 3 * log (1 + A) / (-log δ) := by
  have hx : 0 < -log δ := neg_pos.mpr (log_neg hδ0 hδ1)
  have hB : 0 ≤ log (1 + A) := log_nonneg (by linarith)
  have hgeom := finite_geometric_sum_le hδ0.le hδ1 M
  have hden := inv_one_sub_le_log hδ0 hδ1
  by_cases hA1 : A ≤ 1
  · have hlog := one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + A)
    have hsmall : A ≤ 2 * log (1 + A) := by
      have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1 + A)
      rw [mul_sub, mul_inv_cancel₀ (by linarith : 1 + A ≠ 0), mul_one] at hmul
      have hb := mul_le_mul_of_nonneg_right (by linarith : 1 + A ≤ 2) hB
      nlinarith
    calc
      (∑ i ∈ Finset.range M, min 1 (A * δ ^ i)) ≤
          ∑ i ∈ Finset.range M, A * δ ^ i :=
        Finset.sum_le_sum fun _ _ ↦ min_le_right _ _
      _ = A * ∑ i ∈ Finset.range M, δ ^ i := (Finset.mul_sum _ _ _).symm
      _ ≤ A * (1 + 1 / (-log δ)) :=
        mul_le_mul_of_nonneg_left (hgeom.trans hden) hA
      _ = A + A / (-log δ) := by ring
      _ ≤ 1 + 2 * log (1 + A) / (-log δ) :=
        add_le_add hA1 (div_le_div_of_nonneg_right hsmall hx.le)
      _ ≤ 2 + 3 * log (1 + A) / (-log δ) := by
        have hratio : 0 ≤ log (1 + A) / (-log δ) := div_nonneg hB hx.le
        rw [mul_div_assoc, mul_div_assoc]
        linarith
  · have hApos : 0 < A := by linarith
    have hlogA : 0 ≤ log A := log_nonneg (by linarith)
    have hlogAB : log A ≤ log (1 + A) :=
      log_le_log hApos (by linarith)
    have hhalf : 1 / 2 ≤ log (1 + A) := by
      have htwo := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at htwo
      exact htwo.trans (log_le_log (by norm_num) (by linarith))
    let a : ℕ := ⌈log A / (-log δ)⌉₊
    have hale : log A / (-log δ) ≤ (a : ℝ) := Nat.le_ceil _
    have halt : (a : ℝ) ≤ log A / (-log δ) + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hlogA hx.le)).le
    have hstart : A * δ ^ a ≤ 1 := by
      apply (log_nonpos_iff (mul_nonneg hA (pow_nonneg hδ0.le a))).mp
      rw [log_mul hApos.ne' (pow_pos hδ0 a).ne', log_pow]
      have hmul := (div_le_iff₀ hx).mp hale
      nlinarith
    have hmass : (∑ i ∈ Finset.range M, min 1 (A * δ ^ i)) ≤
        (a : ℝ) + 1 / (1 - δ) := by
      by_cases hMa : M ≤ a
      · calc
          _ ≤ ∑ _i ∈ Finset.range M, (1 : ℝ) :=
            Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
          _ = (M : ℝ) := by simp
          _ ≤ (a : ℝ) := by exact_mod_cast hMa
          _ ≤ (a : ℝ) + 1 / (1 - δ) := le_add_of_nonneg_right (by positivity)
      · have hM : M = a + (M - a) := by omega
        rw [hM, Finset.sum_range_add]
        have hhead : (∑ i ∈ Finset.range a, min 1 (A * δ ^ i)) ≤ (a : ℝ) := by
          calc
            _ ≤ ∑ _i ∈ Finset.range a, (1 : ℝ) :=
              Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
            _ = _ := by simp
        have htail : (∑ i ∈ Finset.range (M - a), min 1 (A * δ ^ (a + i))) ≤
            1 / (1 - δ) := by
          refine (Finset.sum_le_sum fun i _ ↦ ?_).trans
            (finite_geometric_sum_le hδ0.le hδ1 (M - a))
          calc
            min 1 (A * δ ^ (a + i)) ≤ A * δ ^ (a + i) := min_le_right _ _
            _ = (A * δ ^ a) * δ ^ i := by rw [pow_add]; ring
            _ ≤ δ ^ i := by
              simpa using mul_le_mul_of_nonneg_right hstart (pow_nonneg hδ0.le i)
        exact add_le_add hhead htail
    calc
      _ ≤ (a : ℝ) + 1 / (1 - δ) := hmass
      _ ≤ (log A / (-log δ) + 1) + (1 + 1 / (-log δ)) :=
        add_le_add halt hden
      _ = 2 + (log A + 1) / (-log δ) := by ring
      _ ≤ 2 + 3 * log (1 + A) / (-log δ) := by
        refine add_le_add le_rfl ?_
        exact div_le_div_of_nonneg_right (by linarith) hx.le

end Real
