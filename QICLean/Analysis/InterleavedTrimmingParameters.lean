/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reference and threshold budgets at small target overlap

A random subspace can have very small overlap with its target. The
weighted collective-trimming estimate then requires a reference error
quadratic in a guaranteed overlap, and a threshold error linear in that
overlap. These scalar bounds support the corrected interleaved assignment
in ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and the reference argument, lines 1801–1805. Physical construction and
parameter calibration are separate.
-/

namespace Real

/-- Quadratic reference accuracy and linear threshold error control the
actual weighted trimming expression uniformly, even when the incoming
filtered error is close to one. This supports the reference analysis of
ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and lines 1801–1805. The variable `f` is the normalized filtered error. -/
theorem weighted_reference_trim_error_le_filter_add
    {a f epsilon tau : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hepsilonBudget : epsilon ≤ a ^ 2 / 16384)
    (htau : 0 ≤ tau) (htauBudget : tau ≤ a / 256) :
    let theta := a / 64
    (1 + theta) * ((1 + theta) * f + (1 + 1 / theta) * epsilon + 2 * tau) +
      (1 + 1 / theta) * epsilon ≤ f + a / 16 := by
  intro theta
  have htheta : 0 < theta := by dsimp only [theta]; positivity
  have htheta1 : theta ≤ 1 / 64 := by dsimp only [theta]; linarith
  have haSq : a ^ 2 ≤ a := by nlinarith
  have hcoef : (1 + theta) ^ 2 ≤ 1 + 129 * a / 4096 := by
    dsimp only [theta]
    nlinarith
  have hfilter : (1 + theta) ^ 2 * f ≤ f + 129 * a / 4096 := by
    have h := mul_le_mul_of_nonneg_right hcoef hf0
    have h' := mul_nonneg (by positivity : 0 ≤ 129 * a / 4096) (sub_nonneg.mpr hf1)
    nlinarith
  have hepsilonCoef : (2 + theta) * (1 + 1 / theta) ≤ 128 / a + 4 := by
    have heq : (2 + theta) * (1 + 1 / theta) = 128 / a + 3 + theta := by
      dsimp only [theta]
      field_simp
      ring
    rw [heq]
    linarith
  have hepsilonTerm : (2 + theta) * (1 + 1 / theta) * epsilon ≤
      a / 128 + a / 4096 := by
    calc
      _ ≤ (128 / a + 4) * epsilon := mul_le_mul_of_nonneg_right hepsilonCoef hepsilon
      _ ≤ (128 / a + 4) * (a ^ 2 / 16384) :=
        mul_le_mul_of_nonneg_left hepsilonBudget (by positivity)
      _ = a / 128 + a ^ 2 / 4096 := by
        field_simp
        ring
      _ ≤ a / 128 + a / 4096 := by linarith
  have htauTerm : 2 * (1 + theta) * tau ≤ 65 * a / 8192 := by
    calc
      _ ≤ (65 / 32 : ℝ) * (a / 256) :=
        mul_le_mul (by linarith : 2 * (1 + theta) ≤ 65 / 32)
          htauBudget htau (by norm_num)
      _ = _ := by ring
  have hexpand :
      (1 + theta) * ((1 + theta) * f + (1 + 1 / theta) * epsilon + 2 * tau) +
        (1 + 1 / theta) * epsilon =
      (1 + theta) ^ 2 * f + (2 + theta) * (1 + 1 / theta) * epsilon +
        2 * (1 + theta) * tau := by ring
  rw [hexpand]
  linarith

end Real
