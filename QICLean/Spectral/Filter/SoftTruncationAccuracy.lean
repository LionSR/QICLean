/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Filter.SoftTruncationCoercivity
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
lemma Real.softTruncation_order_error_le_one_fourth (m : ℕ) (hm : 0 < m) :
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

/-- For scale `c * m` with `0 < c`, every order `m` above one affine logarithmic bound
satisfies the corrected reverse cutoff condition, bounds the scalar correction by `c / 4`
and makes the exponential residual at most the prescribed budget. Supporting ALVV,
arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268, through
the corrected exponential-moment argument. -/
lemma softTruncation_scaled_order_bounds_of_le (c eta rho : ℝ) (m : ℕ) (hc : 0 < c)
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hmc : 34 + c / 2 + 2 * eta + 16 * log (80 / rho) ≤ c * m) :
    0 < m ∧ 10 ≤ c * (m : ℝ) / 2 ∧
      let alpha := c * (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m
      0 ≤ alpha ∧ alpha ≤ c / 4 ∧ 17 + eta + alpha ≤ c * (m : ℝ) / 2 ∧
      80 * exp ((17 + eta + alpha) / 8 - c * (m : ℝ) / 16) ≤ rho := by
  have hlog : 0 ≤ log (80 / rho) := log_nonneg ((one_le_div hrho).mpr (by linarith only [hrho1]))
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [Nat.cast_zero, mul_zero] at hmc
      linarith only [hmc, hc, heta, hlog]
    · exact h
  have ha := softTruncation_order_error_le_one_fourth m hm
  have hac : c * (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m ≤ c / 4 := by
    have hmul := mul_le_mul_of_nonneg_left ha hc.le
    calc
      _ = c * ((m : ℝ) / 2 * (1 / 2 : ℝ) ^ m) := by ring
      _ ≤ c * (1 / 4) := hmul
      _ = c / 4 := by ring
  refine ⟨hm, by linarith only [hmc, hc, heta, hlog], ?_⟩
  intro alpha
  refine ⟨by dsimp only [alpha]; positivity, hac, ?_, ?_⟩
  · change 17 + eta + c * (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m ≤ _
    linarith only [hmc, hlog, hac]
  · calc
      _ ≤ 80 * exp (-log (80 / rho)) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        change (17 + eta + c * (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m) / 8 - c * (m : ℝ) / 16 ≤ _
        linarith only [hmc, hac]
      _ = rho := by
        rw [exp_neg, exp_log (div_pos (by norm_num) hrho)]
        field_simp

/-- An explicit order, uniform in all physical data, satisfies the corrected
reverse cutoff condition and makes its exponential residual at most the
prescribed budget. This is the case `c = 1` of
`Real.softTruncation_scaled_order_bounds_of_le`. Supporting ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255, through the corrected exponential-moment argument. -/
lemma exists_softTruncation_order_of_residual_budget
    (eta rho : ℝ) (heta : 0 ≤ eta) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ m : ℕ, m = ⌈35 + 2 * eta + 16 * log (80 / rho)⌉₊ ∧
      0 < m ∧ 10 ≤ (m : ℝ) / 2 ∧
      let alpha := (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m
      0 ≤ alpha ∧ alpha ≤ 1 / 4 ∧ 17 + eta + alpha ≤ (m : ℝ) / 2 ∧
      80 * exp ((17 + eta + alpha) / 8 - (m : ℝ) / 16) ≤ rho := by
  have hmcast : 35 + 2 * eta + 16 * log (80 / rho) ≤
      (⌈35 + 2 * eta + 16 * log (80 / rho)⌉₊ : ℝ) := Nat.le_ceil _
  have h := softTruncation_scaled_order_bounds_of_le 1 eta rho
    ⌈35 + 2 * eta + 16 * log (80 / rho)⌉₊ one_pos heta hrho hrho1
    (by rw [one_mul]; linarith only [hmcast])
  simp only [one_mul] at h
  exact ⟨_, rfl, h⟩

end Real

section SoftTruncationScaledAccuracy

/-!
# A compatible order for soft truncation at three times its order

The logarithmic order controls both the reverse physical cutoff and the residual while leaving
all heat times strictly below the cluster threshold. Supporting the corrected moment route to
ALVV, arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268.
-/

namespace Real

/-- One explicit order controls the correction, the reverse cutoff and the requested residual
when scale is three times order. This is the case `c = 3` of
`Real.softTruncation_scaled_order_bounds_of_le`. Supporting the corrected moment route to ALVV,
arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268. -/
lemma exists_softTruncation_scaled_order_of_residual_budget
    (eta rho : ℝ) (heta : 0 ≤ eta) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ m : ℕ, m = ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ ∧
      0 < m ∧ 10 ≤ (3 * (m : ℝ)) / 2 ∧
      let alpha := (3 * (m : ℝ)) / 2 * (1 / 2 : ℝ) ^ m
      0 ≤ alpha ∧ alpha ≤ 3 / 4 ∧ 17 + eta + alpha ≤ (3 * (m : ℝ)) / 2 ∧
      80 * exp ((17 + eta + alpha) / 8 - (3 * (m : ℝ)) / 16) ≤ rho := by
  have hmcast : 12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho) ≤
      (⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ : ℝ) := Nat.le_ceil _
  exact ⟨_, rfl, softTruncation_scaled_order_bounds_of_le 3 eta rho
    ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ (by norm_num) heta hrho
    hrho1 (by linarith only [hmcast])⟩

end Real

end SoftTruncationScaledAccuracy
