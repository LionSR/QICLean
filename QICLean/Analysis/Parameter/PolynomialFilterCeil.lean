/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ceiling scales for polynomial filters

These scalar estimates control the actual natural ceiling used in the
polynomial-filter count. They support ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, and the dyadic argument at
lines 1112–1128. No physical operator, filter, or rank estimate is assumed.
-/

namespace Real

/-- The ceiling of A v²/g is bounded above by (A+1)v²/g and below by A.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
theorem ceil_quadratic_scale_bounds (A v g : ℝ) (hA : 1 ≤ A) (hv : 1 ≤ v)
    (hg : 0 < g) (hg1 : g ≤ 1) :
    A * v ^ 2 / g ≤ (⌈A * v ^ 2 / g⌉₊ : ℝ) ∧
      (⌈A * v ^ 2 / g⌉₊ : ℝ) ≤ (A + 1) * v ^ 2 / g ∧
      A ≤ (⌈A * v ^ 2 / g⌉₊ : ℝ) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have hratio : 1 ≤ v ^ 2 / g := (le_div_iff₀ hg).2 (by linarith)
  have hnonneg : 0 ≤ A * v ^ 2 / g :=
    div_nonneg (mul_nonneg hA0 (sq_nonneg v)) hg.le
  have hscale : A ≤ A * v ^ 2 / g := by
    calc
      A = A * 1 := (mul_one A).symm
      _ ≤ A * (v ^ 2 / g) := mul_le_mul_of_nonneg_left hratio hA0
      _ = A * v ^ 2 / g := by ring
  have hlower : A * v ^ 2 / g ≤ (⌈A * v ^ 2 / g⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨hlower, ?_, hscale.trans hlower⟩
  calc
    (⌈A * v ^ 2 / g⌉₊ : ℝ) ≤ A * v ^ 2 / g + 1 :=
      (Nat.ceil_lt_add_one hnonneg).le
    _ ≤ A * v ^ 2 / g + v ^ 2 / g := add_le_add le_rfl hratio
    _ = (A + 1) * v ^ 2 / g := by ring

/-- The actual ceiling scale changes by at most `21/10` when the inverse
width grows by at most two and the logarithmic factor grows by at most one.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. The lower threshold absorbs integer rounding. -/
theorem ceil_quadratic_scale_half_step (A u v g h : ℝ)
    (hA : 100 ≤ A) (hu : 100 ≤ u) (hv : 1 ≤ v) (hvu : v ≤ u + 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhalf : g ≤ 2 * h) :
    let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
    let ell' : ℕ := ⌈A * v ^ 2 / h⌉₊
    A ≤ (ell : ℝ) ∧ A ≤ (ell' : ℝ) ∧ (ell' : ℝ) ≤ 21 / 10 * (ell : ℝ) := by
  intro ell ell'
  obtain ⟨hlower, _hupper, hellA⟩ :=
    ceil_quadratic_scale_bounds A u g (by linarith) (by linarith) hg hg1
  obtain ⟨_hlower', hupper', hellA'⟩ :=
    ceil_quadratic_scale_bounds A v h (by linarith) hv hh hh1
  refine ⟨hellA, hellA', ?_⟩
  have hAup : A + 1 ≤ (101 / 100 : ℝ) * A := by linarith only [hA]
  have hvup : v ≤ (101 / 100 : ℝ) * u := by linarith only [hvu, hu]
  have hinv : 1 / h ≤ 2 / g :=
    (div_le_div_iff₀ hh hg).mpr (by simpa only [one_mul] using hhalf)
  calc
    (ell' : ℝ) ≤ (A + 1) * v ^ 2 / h := hupper'
    _ = ((A + 1) * v ^ 2) * (1 / h) := by ring
    _ ≤ (((101 / 100) * A) * (((101 / 100) * u) ^ 2)) * (2 / g) :=
      mul_le_mul
        (mul_le_mul hAup
          (pow_le_pow_left₀ (by linarith only [hv]) hvup 2)
          (sq_nonneg v) (by positivity))
        hinv (by positivity) (by positivity)
    _ = (2 * (101 / 100) ^ 3) * (A * u ^ 2 / g) := by ring
    _ ≤ (21 / 10) * (A * u ^ 2 / g) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ (21 / 10) * (ell : ℝ) :=
      mul_le_mul_of_nonneg_left hlower (by norm_num)

end Real
