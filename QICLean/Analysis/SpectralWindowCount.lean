/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting narrow spectral windows

The ceiling count of windows of width twice a residual has a uniform
quadratic budget. A lower energy bounded by four gives the coarser budget
used for centered physical hard truncations.

These scalar estimates support ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, lines 955–968. They require no spectral data.
-/

namespace Real

/-- The number of windows of width twice the residual has the stated
quadratic budget. Auxiliary to ALVV, arXiv:1602.08828v2, `lem:hard-trunc`,
lines 955–968. -/
lemma spectral_window_count_bound (eta xi : ℝ) (heta : 0 ≤ eta)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    (⌈eta / (2 * xi)⌉₊ : ℝ) * (xi + xi) ^ 2 ≤ 2 * (eta + 2) * xi := by
  have hc := (Nat.ceil_lt_add_one (div_nonneg heta (by positivity : 0 ≤ 2 * xi))).le
  calc
    _ ≤ (eta / (2 * xi) + 1) * (xi + xi) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 2 * eta * xi + 4 * xi ^ 2 := by field_simp; ring
    _ ≤ 2 * (eta + 2) * xi := by
      nlinarith only [mul_nonneg hxi.le (sub_nonneg.mpr hxi1)]

/-- The common scalar counting budget for a centered lower energy at most
four. Auxiliary to ALVV, arXiv:1602.08828v2, `lem:hard-trunc`,
lines 955–968. -/
lemma spectral_window_budget_bound
    (E0 eta xi w delta : ℝ) (hE0 : 0 ≤ E0) (hE04 : E0 ≤ 4)
    (heta : 0 ≤ eta) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hw : 0 ≤ w) (hdelta : 0 ≤ delta)
    (hsmall : 2 * (6 + eta) * xi ≤ delta * w ^ 2) :
    (⌈(E0 + eta) / (2 * xi)⌉₊ : ℝ) * (xi + xi) ^ 2 ≤
      delta * (w + xi) ^ 2 := by
  calc
    _ ≤ 2 * (E0 + eta + 2) * xi :=
      spectral_window_count_bound (E0 + eta) xi (add_nonneg hE0 heta) hxi hxi1
    _ ≤ 2 * (6 + eta) * xi := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hE04) hxi.le]
    _ ≤ delta * w ^ 2 := hsmall
    _ ≤ delta * (w + xi) ^ 2 := by gcongr; linarith only [hxi]

end Real
