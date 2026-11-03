/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit precision for finite spectral windows

A norm ceiling and a cutoff ceiling control the natural number of windows
in a buffered spectral comparison. The resulting loss is linear in the
positive approximation precision. A positive minimum gives one precision
before the actual norm and cutoff are known.

These are numerical auxiliaries for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1412–1420, with the finite-window count of the
corrected norm-perturbation comparison. No spectral, subspace or matrix
assumption occurs in these scalar estimates.
-/

namespace Real

/-- A common norm and cutoff ceiling bounds the literal finite-window
loss. Auxiliary to the buffered norm comparison used in ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420. -/
theorem finite_window_loss_le_envelope {A M c R xi w : ℝ}
    (hA : 0 ≤ A) (hAM : A ≤ M) (hc : 0 ≤ c) (hcR : c ≤ R)
    (hxi : 0 < xi) (hw : 0 < w) :
    (⌈(c - min (c - 1) (-(A + xi))) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 /
        (w + xi) ^ 2 ≤
      (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2 := by
  have hM : 0 ≤ M := hA.trans hAM
  have hR : 0 ≤ R := hc.trans hcR
  have hwidth : c - min (c - 1) (-(A + xi)) ≤ R + M + xi + 1 := by
    have hlow : c - (R + M + xi + 1) ≤ min (c - 1) (-(A + xi)) :=
      le_min (by linarith only [hM, hR, hxi]) (by linarith only [hAM, hcR])
    linarith only [hlow]
  have hcount := Nat.ceil_mono
    (div_le_div_of_nonneg_right hwidth (by positivity : 0 ≤ 2 * xi))
  have hcountR : (⌈(c - min (c - 1) (-(A + xi))) / (2 * xi)⌉₊ : ℝ) ≤
      (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) := Nat.cast_le.mpr hcount
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcountR (sq_nonneg (2 * xi)))
    (sq_pos_of_pos (add_pos hw hxi)).le

/-- The uniform natural-window loss is at most a linear precision cost
when the precision is at most one. Auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420. -/
theorem finite_window_envelope_le {M R xi w : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hw : 0 < w) :
    (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2 ≤
      2 * xi * (R + M + 4) / w ^ 2 := by
  have hceil : (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) ≤
      (R + M + xi + 1) / (2 * xi) + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (R + M + xi + 1) / (2 * xi))).le
  have hxiSq : xi ^ 2 ≤ xi := by
    nlinarith only [mul_le_mul_of_nonneg_left hxi1 hxi.le]
  have hnum : (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 ≤
      2 * xi * (R + M + 4) := by
    calc
      _ ≤ ((R + M + xi + 1) / (2 * xi) + 1) * (2 * xi) ^ 2 :=
        mul_le_mul_of_nonneg_right hceil (sq_nonneg (2 * xi))
      _ = 2 * xi * (R + M + 1) + 6 * xi ^ 2 := by
        field_simp [hxi.ne']
        ring
      _ ≤ 2 * xi * (R + M + 4) := by nlinarith only [hxiSq]
  have hden : w ^ 2 ≤ (w + xi) ^ 2 :=
    pow_le_pow_left₀ hw.le (le_add_of_nonneg_right hxi.le) 2
  exact (div_le_div_of_nonneg_right hnum (sq_pos_of_pos (add_pos hw hxi)).le).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hw) hden)

/-- An explicit positive precision budget makes the uniform finite-window
loss at most half the requested error. The estimate is numerical and does
not assume a successful spectral comparison. Auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420. -/
theorem finite_window_envelope_le_half_of_precision {M R xi w beta : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hw : 0 < w) (hbudget : xi ≤ beta * w ^ 2 / (4 * (R + M + 4))) :
    (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2 ≤
      beta / 2 := by
  have hbudget' : xi * (4 * (R + M + 4)) ≤ beta * w ^ 2 :=
    (le_div_iff₀ (by positivity : 0 < 4 * (R + M + 4))).mp hbudget
  refine (finite_window_envelope_le hM hR hxi hxi1 hw).trans ?_
  apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
  nlinarith only [hbudget']

/-- A positive precision can be chosen before the actual norm and cutoff.
The same ceiling controls every finite window in the prescribed range.
Auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420. -/
theorem finite_window_precision_parameters {M R w beta : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : 0 < w) (hbeta : 0 < beta) :
    let xi := min 1 (beta * w ^ 2 / (4 * (R + M + 4)))
    0 < xi ∧ xi ≤ 1 ∧ xi ≤ beta * w ^ 2 / (4 * (R + M + 4)) ∧
      (⌈(R + M + xi + 1) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2 ≤
        beta / 2 := by
  intro xi
  have hxi : 0 < xi := lt_min (by norm_num) (by positivity)
  have hxi1 : xi ≤ 1 := min_le_left _ _
  have hbudget : xi ≤ beta * w ^ 2 / (4 * (R + M + 4)) := min_le_right _ _
  exact ⟨hxi, hxi1, hbudget,
    finite_window_envelope_le_half_of_precision hM hR hxi hxi1 hw hbudget⟩

/-- At the soft-cluster cutoffs, an explicit positive precision makes both
uniform window losses at most `tau / 400`. This is a numerical auxiliary,
not a spectral-gap or subspace assumption. Supporting ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420. -/
theorem soft_cluster_window_precision_parameters {M g tau : ℝ}
    (hM : 0 ≤ M) (hg : 0 < g) (htau : 0 < tau) :
    let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
    0 < xi ∧ xi ≤ 1 ∧ xi ≤ tau * g ^ 2 / (20000 * (M + g + 8)) ∧
      (⌈((4 + g) + M + xi + 1) / (2 * xi)⌉₊ : ℝ) * (2 * xi) ^ 2 /
          (g / 5 + xi) ^ 2 ≤ tau / 400 := by
  have hquota : (tau / 200) * (g / 5) ^ 2 / (4 * ((4 + g) + M + 4)) =
      tau * g ^ 2 / (20000 * (M + g + 8)) := by
    rw [show (4 + g) + M + 4 = M + g + 8 by ring]
    field_simp [(by positivity : 0 < M + g + 8).ne']
    ring
  have hparameters := finite_window_precision_parameters hM
    (by positivity : 0 ≤ 4 + g) (by positivity : 0 < g / 5)
    (by positivity : 0 < tau / 200)
  rw [hquota] at hparameters
  intro xi
  obtain ⟨hxi, hxi1, hbudget, hloss⟩ := hparameters
  refine ⟨hxi, hxi1, hbudget, ?_⟩
  simpa only [div_div, show (200 : ℝ) * 2 = 400 by norm_num] using hloss

end Real
