/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# An explicit order for an exponential geometric tail

A logarithmic ceiling chooses an actual truncation order from a positive accuracy budget.
Supporting the corrected cluster approximation used in ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. This scalar choice makes no running-time assertion.
-/

namespace Real

/-- An explicit positive order makes a weighted exponential geometric tail smaller than the
prescribed error. This is an auxiliary parameter choice for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268, with the corrected cluster estimate. -/
lemma exponential_geometric_tail_order (N W b xi : ℝ) (hW : 0 < W)
    (hb0 : 0 < b) (hb1 : b < 1) (hxi : 0 < xi) :
    let r := max 1 ⌈(log (max 1 (N ^ 2)) - log (log (1 + xi / W))) / (-log b)⌉₊
    0 < r ∧ W * (exp (N ^ 2 * b ^ r) - 1) ≤ xi := by
  intro r
  let A := max 1 (N ^ 2)
  let d := log (1 + xi / W)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hd : 0 < d := log_pos (by linarith [div_pos hxi hW])
  have hb : log b < 0 := log_neg hb0 hb1
  have hr : (log A - log d) / (-log b) ≤ (r : ℝ) := by
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have hlog : log A + (r : ℝ) * log b ≤ log d := by
    have hmul := (div_le_iff₀ (neg_pos.mpr hb)).mp hr
    linarith
  have hp : A * b ^ r ≤ d := by
    have he := exp_le_exp.mpr hlog
    rw [exp_add, exp_log hA, exp_nat_mul, exp_log hb0, exp_log hd] at he
    exact he
  have hNd : N ^ 2 * b ^ r ≤ d :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hb0.le _)).trans hp
  have he : exp (N ^ 2 * b ^ r) - 1 ≤ xi / W := by
    have h := exp_le_exp.mpr hNd
    rw [exp_log (by positivity : 0 < 1 + xi / W)] at h
    linarith
  refine ⟨lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  exact (mul_le_mul_of_nonneg_left he hW.le).trans_eq (by field_simp)

end Real
