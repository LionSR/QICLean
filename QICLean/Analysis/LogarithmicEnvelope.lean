/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform logarithmic bounds for sequences

An asymptotic bound by `log (k + 1)` gives a uniform bound by a nonnegative
multiple of `log (k + 2)`. The positive shift includes every initial index,
without imposing a vanishing condition at zero.
-/

open Filter

namespace Asymptotics

/-- If a real sequence is `O(log (k + 1))` at infinity, its absolute value is
bounded at every natural index by `C * log (k + 2)` for some nonnegative `C`.
The finite initial segment is absorbed into the constant, including a possibly
nonzero value at zero. -/
theorem IsBigO.exists_nonneg_abs_le_mul_log_add_two {f : ℕ → ℝ}
    (hf : f =O[atTop] fun k => Real.log ((k : ℝ) + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, |f k| ≤ C * Real.log ((k : ℝ) + 2) := by
  have hlog (k : ℕ) : 0 < Real.log ((k : ℝ) + 2) := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact Real.log_pos (by linarith)
  have hf' : f =O[atTop] fun k => Real.log ((k : ℝ) + 2) := by
    refine hf.trans_le fun k => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ (k : ℝ) + 1)),
      abs_of_pos (hlog k)]
    exact Real.log_le_log (by linarith) (by linarith)
  obtain ⟨C, hC, hbound⟩ := bound_of_isBigO_nat_atTop hf'
  refine ⟨C, hC.le, fun k => ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_pos (hlog k)] using hbound (hlog k).ne'

end Asymptotics
