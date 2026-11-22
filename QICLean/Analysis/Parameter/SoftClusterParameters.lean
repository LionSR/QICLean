/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Existence of soft-truncation residual parameters

A common cutoff first makes the exponential residual small. A sufficiently
large Taylor order then controls the remaining power at truncation scale
three times that order. The two residuals in the five-region construction
can therefore be made arbitrarily small with one choice of parameters.

These are scalar auxiliaries to ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1420.
Only existence is asserted; no bound on the computational cost is included.
-/

namespace Real

/-- A common cutoff and Taylor order control the soft residual for every
energy offset below a prescribed ceiling. This is a scalar auxiliary to
ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem exists_soft_truncation_residual_parameters {B epsilon : ℝ}
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (t T : ℝ), 2 ≤ m ∧ t = 3 * (m : ℝ) ∧ B ≤ T ∧ B ≤ t ∧
      ∀ b : ℝ, b ≤ B →
        3 * (32 * exp (-(T - b) / 8) + (t / m) * (T / t) ^ m) ≤ epsilon := by
  let X := max 1 (192 / epsilon)
  have hX1 : 1 ≤ X := le_max_left _ _
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  let T := B + 8 * log X
  have hBT : B ≤ T := by
    dsimp only [T]
    nlinarith only [log_nonneg hX1]
  have hT : 0 ≤ T := hB.trans hBT
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < epsilon / 18) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * T / 3)
  let m := max 2 (max k n)
  have hm2 : 2 ≤ m := le_max_left _ _
  have hm : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm2)
  have hkm : k ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hnm : n ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hTm : T ≤ 3 * (m : ℝ) / 2 := by
    have hnmR : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    linarith only [hn, hnmR]
  refine ⟨m, 3 * (m : ℝ), T, hm2, rfl, hBT, ?_, ?_⟩
  · linarith only [hBT, hTm, hm]
  intro b hb
  have hbase : T / (3 * (m : ℝ)) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity : 0 < 3 * (m : ℝ))).mpr (by linarith only [hTm])
  have hpower : (T / (3 * (m : ℝ))) ^ m ≤ epsilon / 18 :=
    (pow_le_pow_left₀ (by positivity) hbase m).trans
      ((pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hkm).trans hk.le)
  have harg : -(T - b) / 8 ≤ -log X := by
    dsimp only [T]
    linarith only [hb]
  have hExp : exp (-(T - b) / 8) ≤ 1 / X := by
    simpa only [exp_neg, exp_log hX, one_div] using exp_le_exp.mpr harg
  have hXquota : 192 / epsilon ≤ X := le_max_right _ _
  have hsmall : 32 / X ≤ epsilon / 6 := by
    have hquota := (div_le_iff₀ hepsilon).mp hXquota
    apply (div_le_iff₀ hX).mpr
    nlinarith only [hquota]
  have hExpSmall : 32 * exp (-(T - b) / 8) ≤ epsilon / 6 :=
    (mul_le_mul_of_nonneg_left hExp (by norm_num)).trans (by
      simpa only [mul_one_div] using hsmall)
  rw [mul_div_cancel_right₀ 3 hm.ne']
  nlinarith only [hExpSmall, hpower]

/-- One common cutoff and one Taylor order satisfy both three-region
residual budgets for every positive gap and requested error. This is an
existence auxiliary for ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1420; it makes no computational-cost assertion. -/
theorem exists_soft_cluster_parameters {g tau : ℝ} (hg : 0 < g) (htau : 0 < tau) :
    ∃ (m : ℕ) (t T : ℝ), 2 ≤ m ∧ t = 3 * (m : ℝ) ∧
      156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
      3 * (32 * exp (-(T - g / 40 - 24) / 8) +
        (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
      3 * (32 * exp (-(T - 156 - 2 * g) / 8) +
        (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 := by
  obtain ⟨m, t, T, hm, ht, hBT, hBt, hres⟩ :=
    exists_soft_truncation_residual_parameters (by positivity : 0 ≤ 156 + 2 * g)
      (by positivity : 0 < tau * g / 1000000)
  have hsmall : g / 40 + 24 ≤ 156 + 2 * g := by linarith only [hg]
  refine ⟨m, t, T, hm, ht, hBt, hBT, hsmall.trans hBT, ?_, ?_⟩
  · simpa only [sub_add_eq_sub_sub] using hres (g / 40 + 24) hsmall
  · simpa only [sub_add_eq_sub_sub] using hres (156 + 2 * g) le_rfl

end Real
