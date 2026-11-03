/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Natural rank budgets from logarithmic estimates

The two elementary rounding proofs are moved unchanged from
`TNLean/MPS/AreaLaw/PhysicalDGGlobalApproximation.lean`. They convert a
logarithmic natural-number estimate to one integer exponential budget and
bound the logarithm of that rounded exponential. No physical or spectral
hypothesis is involved. They support the passage from fixed cuts to global
MPS approximation in ALVV, arXiv:1602.08828v2, lines 1080–1086 and 1096–1105.
-/

namespace Nat

/-- An integer rank below a logarithmic budget is bounded by the ground-space
factor times a single rounded exponential. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem 4.9, global approximation at source line 1086. -/
theorem le_mul_ceil_exp_of_log_le {s r : ℕ} (hr : 1 ≤ r) (E : ℝ)
    (hlog : Real.log (s : ℝ) ≤ Real.log (r : ℝ) + E) :
    s ≤ r * ⌈Real.exp E⌉₊ := by
  by_cases hs : s = 0
  · simp only [hs, Nat.zero_le]
  · have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hspos, Real.exp_add, Real.exp_log hrpos] at hexp
    have hbound : (s : ℝ) ≤ ((r * ⌈Real.exp E⌉₊ : ℕ) : ℝ) := by
      calc
        (s : ℝ) ≤ (r : ℝ) * Real.exp E := hexp
        _ ≤ (r : ℝ) * (⌈Real.exp E⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) hrpos.le
        _ = _ := by rw [Nat.cast_mul]
    exact_mod_cast hbound

end Nat

namespace Real

/-- Rounding a nonnegative exponential costs at most one in its logarithm.
Auxiliary to the integer bond bound in ALVV, arXiv:1602.08828v2,
Theorem 4.9, source line 1086. -/
theorem log_ceil_exp_le_add_one (E : ℝ) (hE : 0 ≤ E) :
    1 ≤ ⌈Real.exp E⌉₊ ∧ Real.log (⌈Real.exp E⌉₊ : ℝ) ≤ E + 1 := by
  have hexp : 1 ≤ Real.exp E := Real.one_le_exp hE
  have hB : 1 ≤ ⌈Real.exp E⌉₊ := by exact_mod_cast hexp.trans (Nat.le_ceil _)
  have hBpos : (0 : ℝ) < (⌈Real.exp E⌉₊ : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hB)
  have hupper : (⌈Real.exp E⌉₊ : ℝ) ≤ 2 * Real.exp E := by
    have hceil := (Nat.ceil_lt_add_one (Real.exp_nonneg E)).le
    linarith only [hceil, hexp]
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  refine ⟨hB, ?_⟩
  calc
    Real.log (⌈Real.exp E⌉₊ : ℝ) ≤ Real.log (2 * Real.exp E) :=
      Real.log_le_log hBpos hupper
    _ = Real.log 2 + E := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero E), Real.log_exp]
    _ ≤ E + 1 := by linarith only [hlog2]

end Real
