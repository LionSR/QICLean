/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform absorption of logarithmic constants

A fixed logarithmic expression is eventually smaller than every positive
multiple of a positive power. This is the scalar step needed when a
constant must be chosen before all gaps, chain lengths and accuracies in
ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024, and the
algorithmic parameter selection, lines 1797–1805.
-/

open Filter

namespace Real

/-- A logarithmic expression is bounded by a prescribed positive multiple
of any positive power at a sufficiently large point, beyond every given
threshold. This follows from the Mathlib logarithm-versus-power limit and
supports the uniform constants in ALVV, arXiv:1602.08828v2,
Theorem `t:ais`, lines 1010–1024, and lines 1797–1805. -/
theorem exists_log_rpow_absorption (a b c M p : ℝ)
    (hb : 0 ≤ b) (hc : 0 < c) (hp : 0 < p) :
    ∃ A : ℝ, 1 ≤ A ∧ M ≤ A ∧ a + b * log (A + 1) ≤ c * A ^ p := by
  have hlog : log =o[atTop] (fun x : ℝ ↦ x ^ p) := isLittleO_log_rpow_atTop hp
  have hconst : (fun _ : ℝ ↦ a + b * log 2) =o[atTop] (fun x : ℝ ↦ x ^ p) := by
    simpa only [Function.comp_def, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop (a + b * log 2)).comp_tendsto
        (tendsto_rpow_atTop hp)
  have hsmall : (fun x : ℝ ↦ a + b * log 2 + b * log x) =o[atTop]
      (fun x : ℝ ↦ x ^ p) := hconst.add (hlog.const_mul_left b)
  obtain ⟨A, hA, hbound⟩ :=
    ((eventually_ge_atTop (max 1 M)).and (hsmall.def hc)).exists
  have hA1 : 1 ≤ A := (le_max_left 1 M).trans hA
  have hAM : M ≤ A := (le_max_right 1 M).trans hA
  have hlogA : log (A + 1) ≤ log 2 + log A := by
    calc
      log (A + 1) ≤ log (2 * A) := log_le_log (by linarith) (by linarith)
      _ = log 2 + log A := log_mul (by norm_num) (by linarith)
  refine ⟨A, hA1, hAM, ?_⟩
  calc
    a + b * log (A + 1) ≤ a + b * (log 2 + log A) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hlogA hb) a
    _ = a + b * log 2 + b * log A := by ring
    _ ≤ ‖a + b * log 2 + b * log A‖ := le_abs_self _
    _ ≤ c * ‖A ^ p‖ := hbound
    _ = c * A ^ p := by rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (by linarith) _)]

/-- A sufficiently large common constant absorbs the cube of its own
logarithmic expression, uniformly before any subsequent physical data.
This is a scalar auxiliary for the parameter choice in ALVV,
arXiv:1602.08828v2, lines 1797–1805. -/
theorem exists_log_cube_absorption_constant (a b K M : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 < K) :
    ∃ A : ℝ, 1 ≤ A ∧ M ≤ A ∧ K * (a + b * log (A + 1)) ^ 3 ≤ A := by
  let c := (1 / K) ^ (1 / 3 : ℝ)
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨A, hA, hM, hbound⟩ :=
    exists_log_rpow_absorption a b c M (1 / 3) hb hc (by norm_num)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hbase : 0 ≤ a + b * log (A + 1) := by
    have hlog : 0 ≤ log (A + 1) := log_nonneg (by linarith)
    positivity
  have hcubeA : (A ^ (1 / 3 : ℝ)) ^ 3 = A := by
    simpa only [Nat.cast_ofNat, one_div] using rpow_inv_natCast_pow hA0 (by decide : 3 ≠ 0)
  have hcubeC : c ^ 3 = 1 / K := by
    dsimp only [c]
    simpa only [Nat.cast_ofNat, one_div] using
      rpow_inv_natCast_pow (by positivity : 0 ≤ 1 / K) (by decide : 3 ≠ 0)
  have hpow := pow_le_pow_left₀ hbase hbound 3
  rw [mul_pow, hcubeA, hcubeC] at hpow
  refine ⟨A, hA, hM, ?_⟩
  have h := mul_le_mul_of_nonneg_left hpow hK.le
  have heq : K * (1 / K * A) = A := by field_simp [hK.ne']
  exact h.trans_eq heq

end Real
