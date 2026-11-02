/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncationCoercivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# An explicit order for the corrected soft-truncation residual

The scalar correction is uniformly bounded by one quarter. A single ceiling
of a logarithmic expression then ensures both the reverse cutoff condition
and any requested positive residual budget at equal scale and order.

These parameters support the corrected exponential-moment route to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. They do not establish
the printed uniform energy estimate.
-/

/-- The equal-scale scalar correction is bounded uniformly by one quarter. Supporting the
corrected soft/hard comparison for ALVV, arXiv:1602.08828v2, `def:soft-trunc`, lines 1178–1185. -/
theorem Real.softTruncation_order_error_le_one_fourth (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m ≤ 1 / 4 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hk : (k + 1 : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
  have heq : ((k + 1 : ℕ) : ℝ) / 2 * (1 / 2 : ℝ) ^ (k + 1) =
      (k + 1 : ℝ) / (4 * (2 : ℝ) ^ k) := by
    rw [Nat.cast_add, Nat.cast_one, pow_succ, div_pow, one_pow]
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (2 : ℝ) ^ k)).mpr
  linarith only [hk]

namespace Real

/-- An explicit order, uniform in all physical data, satisfies the corrected
reverse cutoff condition and makes its exponential residual at most the
prescribed budget. Supporting ALVV, arXiv:1602.08828v2, `lem:exp-approx`,
lines 1195–1255, through the corrected exponential-moment argument. -/
theorem exists_softTruncation_order_of_residual_budget
    (eta rho : ℝ) (heta : 0 ≤ eta) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ m : ℕ, m = ⌈35 + 2 * eta + 16 * log (80 / rho)⌉₊ ∧
      0 < m ∧ 10 ≤ (m : ℝ) / 2 ∧
      let alpha := (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m
      0 ≤ alpha ∧ alpha ≤ 1 / 4 ∧ 17 + eta + alpha ≤ (m : ℝ) / 2 ∧
      80 * exp ((17 + eta + alpha) / 8 - (m : ℝ) / 16) ≤ rho := by
  let m := ⌈35 + 2 * eta + 16 * log (80 / rho)⌉₊
  have hlog : 0 ≤ log (80 / rho) := log_nonneg ((one_le_div hrho).mpr (by linarith only [hrho1]))
  have hmcast : 35 + 2 * eta + 16 * log (80 / rho) ≤ (m : ℝ) := Nat.le_ceil _
  have hm : 0 < m := by
    have hp : (0 : ℝ) < m := by linarith only [hmcast, heta, hlog]
    exact_mod_cast hp
  have ha := softTruncation_order_error_le_one_fourth m hm
  refine ⟨m, rfl, hm, by linarith only [hmcast, heta, hlog], ?_⟩
  intro alpha
  refine ⟨by dsimp only [alpha]; positivity, ha, ?_, ?_⟩
  · change 17 + eta + (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m ≤ _
    linarith only [hmcast, hlog, ha]
  · calc
      _ ≤ 80 * exp (-log (80 / rho)) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        change (17 + eta + (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m) / 8 - (m : ℝ) / 16 ≤ _
        linarith only [hmcast, ha]
      _ = rho := by
        rw [exp_neg, exp_log (div_pos (by norm_num) hrho)]
        field_simp

end Real
