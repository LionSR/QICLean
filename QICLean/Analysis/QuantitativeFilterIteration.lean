/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableFilterTrimmingIteration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A logarithmic bound for repeated filtering and trimming

The numerical recurrence for the final refinement in ALVV,
arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640, reaches any positive
error after a logarithmic number of steps. These auxiliary estimates concern
the recurrence; identifying its error parameter with the energy tolerance in
the algorithm requires a separate spectral argument.
-/

namespace Real

/-- Exponential decay for the contraction factor in the stable refinement
recurrence, used in ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1813. -/
theorem filter_trim_contraction_pow_le_exp {c : ℝ} (hc1 : c ≤ 1)
    (n : ℕ) : (1 - c / 4) ^ n ≤ exp (-(c / 4) * n) := by
  have hq : 0 ≤ 1 - c / 4 := by linarith
  have hbase : 1 - c / 4 ≤ exp (-(c / 4)) := by
    linarith [add_one_le_exp (-(c / 4))]
  simpa only [← exp_nat_mul, mul_comm (n : ℝ)] using
    pow_le_pow_left₀ hq hbase n

/-- A prescribed logarithmic number of refinement steps reaches the target error.
This is a numerical consequence of the recurrence used in ALVV,
arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640. -/
theorem filter_trim_iterate_le_of_log_bound {c η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hη0 : 0 < η) (hη : η ≤ 1) (u : ℕ → ℝ) (hu : u 0 ≤ 1 / 2)
    (hstep : ∀ n, u n ≤ 1 / 2 → u (n + 1) ≤ (1 - c / 4) * u n + c * η / 8)
    (n : ℕ) (hn : 4 / c * log (1 / η) ≤ n) : u n ≤ η := by
  have hb := (filter_trim_iterate_le hc hc1 hη0.le hη u hu hstep).2 n
  have hd : log (1 / η) ≤ c / 4 * n := by
    calc
      _ = (c / 4) * (4 / c * log (1 / η)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  have hexp : exp (-(c / 4) * n) ≤ η := by
    rw [← exp_log hη0, exp_le_exp]
    simpa only [one_div, log_inv, neg_neg, neg_mul] using neg_le_neg hd
  have hpow : (1 - c / 4) ^ n ≤ η :=
    (filter_trim_contraction_pow_le_exp hc1 n).trans hexp
  have hs := mul_le_mul_of_nonneg_left hu
    (pow_nonneg (by linarith : 0 ≤ 1 - c / 4) n)
  linarith

/-- An explicit positive number of steps suffices for the refinement recurrence.
The additional step also covers target error one. This is an auxiliary bound for
ALVV, arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640. -/
theorem filter_trim_iterate_ceil_log_le {c η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hη0 : 0 < η) (hη : η ≤ 1) (u : ℕ → ℝ) (hu : u 0 ≤ 1 / 2)
    (hstep : ∀ n, u n ≤ 1 / 2 → u (n + 1) ≤ (1 - c / 4) * u n + c * η / 8) :
    u (⌈4 / c * log (1 / η)⌉₊ + 1) ≤ η := by
  apply filter_trim_iterate_le_of_log_bound hc hc1 hη0 hη u hu hstep
  exact (Nat.le_ceil _).trans (by push_cast; linarith)

end Real
