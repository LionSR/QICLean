/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar energy-weighted decay of a positive-contraction power

A finite geometric sum bounds the energy weight in a contraction power. The second estimate
retains an explicit lower excitation energy and a sufficient integer power threshold.
These are conditional scalar auxiliaries for ALVV, arXiv:1602.08828v2, `t:alg1`, final power
step, lines 1811–1815. They do not construct the repeated trimmed subspaces or their compressed
eigenvectors, and they make no assertion about the source's overlap recurrence.
-/

namespace Real

/-- A geometric-sum bound for an energy weight on the unit interval. Conditional scalar
auxiliary to ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1811–1815. -/
theorem mul_one_sub_pow_le_inv_add_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (tau : ℕ) :
    x * (1 - x) ^ tau ≤ 1 / ((tau : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (tau : ℝ) + 1)).mpr
  have hsum := Finset.sum_le_sum (s := Finset.range (tau + 1))
    (f := fun _ ↦ (1 - x) ^ tau) (g := fun i ↦ (1 - x) ^ i)
    (fun i hi ↦ pow_le_pow_of_le_one (sub_nonneg.mpr hx1) (sub_le_self 1 hx0)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hgeom := geom_sum_mul_neg (1 - x) (tau + 1)
  nlinarith only [mul_le_mul_of_nonneg_left hsum hx0, hgeom,
    pow_nonneg (sub_nonneg.mpr hx1) (tau + 1)]

/-- The energy-weighted squared power is controlled by the lowest excitation energy once
its integer threshold holds. Conditional scalar auxiliary to ALVV,
arXiv:1602.08828v2, `t:alg1`, final power step, lines 1811–1815. -/
theorem energy_mul_one_sub_div_pow_le {A gamma s : ℝ} (hA : 0 < A)
    (hgamma : 0 < gamma) (hgs : gamma ≤ s) (hsA : s ≤ A) (tau : ℕ)
    (hbudget : A ≤ ((tau : ℝ) + 1) * gamma) :
    s * (1 - s / A) ^ (2 * tau) ≤ gamma * (1 - gamma / A) ^ tau := by
  have hunit := mul_one_sub_pow_le_inv_add_one
    (div_nonneg (hgamma.le.trans hgs) hA.le) ((div_le_one hA).mpr hsA) tau
  have hcoef : A * (1 / ((tau : ℝ) + 1)) ≤ gamma := by
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hbudget])
  have hbase : 0 ≤ 1 - s / A := sub_nonneg.mpr ((div_le_one hA).mpr hsA)
  have hmono : (1 - s / A) ^ tau ≤ (1 - gamma / A) ^ tau :=
    pow_le_pow_left₀ hbase
      (sub_le_sub_left (div_le_div_of_nonneg_right hgs hA.le) 1) tau
  calc
    s * (1 - s / A) ^ (2 * tau) =
        (A * (s / A * (1 - s / A) ^ tau)) * (1 - s / A) ^ tau := by
          simp only [two_mul, pow_add, ← mul_assoc, mul_div_cancel₀ s hA.ne']
    _ ≤ (A * (1 / ((tau : ℝ) + 1))) * (1 - s / A) ^ tau :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hunit hA.le)
        (pow_nonneg hbase tau)
    _ ≤ gamma * (1 - gamma / A) ^ tau :=
      mul_le_mul hcoef hmono (pow_nonneg hbase tau) hgamma.le

end Real
