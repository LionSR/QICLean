/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolynomialFilterCounts
import Mathlib.Tactic.FieldSimp

/-!
# A finite index for dyadic polynomial-filter counts

At a fixed positive initial width, the actual natural ceiling eventually
exceeds every prescribed finite dimension. A concrete natural index gives
this conclusion, without assuming termination or a count-envelope crossing.
The result supports ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. It is a scalar statement: no
physical filter or suppression estimate is assumed.
-/

namespace Real

/-- The actual count at a finite dyadic index exceeds any prescribed natural
bound. The degree is the same ceiling as in the physical filter construction.
The explicit index is finite even when the requested bound is zero.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_dyadic_polynomial_filter_count_ge (C v : ℝ) (m N : ℕ)
    (hC : 1 ≤ C) (hv : 0 < v) (hm : 2 ≤ m) :
    ∃ j : ℕ,
      let g := min (v / (6 * (2 : ℝ) ^ j)) 1
      let u := 1 + log (m : ℝ) + log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      N ≤ ell ∧ N ≤ D := by
  let j : ℕ := ⌈(N : ℝ) * v / (6 * C)⌉₊
  refine ⟨j, ?_⟩
  intro g u ell D
  let w := v / (6 * (2 : ℝ) ^ j)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hw : 0 < w := by dsimp only [w]; positivity
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgw : g ≤ w := min_le_left _ _
  have hlogm : 0 ≤ log (m : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogm, hlogg]
  have hu2 : 1 ≤ u ^ 2 := by nlinarith only [hu]
  have hpow : (j : ℝ) ≤ (2 : ℝ) ^ j := by
    exact_mod_cast (Nat.le_of_lt j.lt_two_pow_self)
  have hratio : (N : ℝ) * v / (6 * C) ≤ (2 : ℝ) ^ j :=
    (Nat.le_ceil _).trans hpow
  have hNw : (N : ℝ) * w ≤ C := by
    dsimp only [w]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 6 * 2 ^ j)]
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * C)).mp hratio
    nlinarith only [h]
  have hNdiv : (N : ℝ) ≤ C / g := (le_div_iff₀ hg).mpr
    ((mul_le_mul_of_nonneg_left hgw (Nat.cast_nonneg N)).trans hNw)
  have hscale : C / g ≤ C * u ^ 2 / g :=
    div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hu2 hCpos.le) hg.le
  have hNell : N ≤ ell := by
    exact_mod_cast hNdiv.trans (hscale.trans (Nat.le_ceil _))
  have hellR : C ≤ (ell : ℝ) :=
    (ceil_quadratic_scale_bounds C u g hC hu hg hg1).2.2
  have hell : 1 ≤ ell := by exact_mod_cast hC.trans hellR
  have hellsq : ell ≤ ell ^ 2 := Nat.le_self_pow (by decide) ell
  have hellbase : ell ≤ m * ell ^ 2 := hellsq.trans
    (by simpa only [one_mul] using Nat.mul_le_mul_right (ell ^ 2) (by omega : 1 ≤ m))
  have hbaseD : m * ell ^ 2 ≤ D := Nat.le_self_pow (by omega : 22 * ell ≠ 0) _
  exact ⟨hNell, hNell.trans (hellbase.trans hbaseD)⟩

end Real
