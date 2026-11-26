/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dyadic growth of polynomial-filter counts

The count is evaluated at the actual natural ceiling of the filter scale.
A fixed large count base absorbs the finite rounding terms in the dyadic
argument of ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. This is a scalar auxiliary; no physical rank or suppression
estimate is an assumption or conclusion.

It also contains the following results.

* `Real.ceil_quadratic_scale_bounds`, `Real.ceil_quadratic_scale_half_step`: ceiling scales for
  polynomial filters.
* `Real.log_polynomial_filter_base_le`, `Real.polynomial_filter_count_bounds`: logarithms of the
  actual polynomial-filter counts.
-/

section PolynomialFilterCeil

/-!
## Ceiling scales for polynomial filters

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

end PolynomialFilterCeil

section PolynomialFilterCounts

namespace Real

/-- Halving the width enlarges the logarithm of the actual natural count by
at most `13/6`. The count base is fixed before both widths. This finite-scale
auxiliary supports ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem log_polynomial_filter_count_half_step (A : ℝ) (m : ℕ) (g h : ℝ)
    (hA : 100 ≤ A) (hm : 100 ≤ log (m : ℝ))
    (hg : 0 < g) (hg1 : g ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhalf : g ≤ 2 * h) :
    let u := 1 + log (m : ℝ) + log (1 / g)
    let v := 1 + log (m : ℝ) + log (1 / h)
    let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
    let ell' : ℕ := ⌈A * v ^ 2 / h⌉₊
    let D := (m * ell ^ 2) ^ (22 * ell)
    let D' := (m * ell' ^ 2) ^ (22 * ell')
    100 ≤ log (D : ℝ) ∧ log (D' : ℝ) ≤ (13 / 6) * log (D : ℝ) := by
  intro u v ell ell' D D'
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogh : 0 ≤ log (1 / h) := log_nonneg ((one_le_div hh).mpr hh1)
  have hu : 100 ≤ u := by dsimp only [u]; linarith only [hm, hlogg]
  have hv : 1 ≤ v := by dsimp only [v]; linarith only [hm, hlogh]
  have hinv : 1 / h ≤ 2 / g :=
    (div_le_div_iff₀ hh hg).mpr (by simpa only [one_mul] using hhalf)
  have hlogratio : log (1 / h) ≤ log (1 / g) + 1 := by
    have hb := log_le_log (by positivity : 0 < 1 / h) hinv
    rw [show (2 : ℝ) / g = 2 * (1 / g) by ring,
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (1 / g) ≠ 0)] at hb
    have hlog2 : log (2 : ℝ) ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
        log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hb, hlog2]
  obtain ⟨hellA, hellA', hscale⟩ :=
    ceil_quadratic_scale_half_step A u v g h hA hu hv
      (by dsimp only [u, v]; linarith only [hlogratio]) hg hg1 hh hh1 hhalf
  have hell : 100 ≤ (ell : ℝ) := hA.trans hellA
  have hell' : 100 ≤ (ell' : ℝ) := hA.trans hellA'
  have hell0 : 0 < (ell : ℝ) := by linarith only [hell]
  have hell'0 : 0 < (ell' : ℝ) := by linarith only [hell']
  have hm_nat : m ≠ 0 := by rintro rfl; norm_num at hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm_nat
  let B := log (m : ℝ) + 2 * log (ell : ℝ)
  let B' := log (m : ℝ) + 2 * log (ell' : ℝ)
  have hB : 100 ≤ B := by
    have hb := log_nonneg (show 1 ≤ (ell : ℝ) by linarith only [hell])
    dsimp only [B]
    linarith only [hm, hb]
  have hlogscale : log (ell' : ℝ) ≤ log (ell : ℝ) + 11 / 10 := by
    have hb := log_le_log hell'0 hscale
    rw [log_mul (by norm_num : (21 / 10 : ℝ) ≠ 0) hell0.ne'] at hb
    have hlogratio' : log (21 / 10 : ℝ) ≤ 11 / 10 := by
      simpa only [show (21 / 10 : ℝ) - 1 = 11 / 10 by norm_num] using
        log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 10)
    linarith only [hb, hlogratio']
  have hBscale : B' ≤ (511 / 500) * B := by
    dsimp only [B, B'] at *
    linarith only [hB, hlogscale]
  have hcountLog (n : ℕ) (hn : 0 < (n : ℝ)) :
      log ((((m * n ^ 2) ^ (22 * n)) : ℕ) : ℝ) =
        22 * (n : ℝ) * (log (m : ℝ) + 2 * log (n : ℝ)) := by
    simp only [Nat.cast_pow, Nat.cast_mul, log_pow,
      log_mul hm0.ne' (pow_ne_zero 2 hn.ne')]
    push_cast
    ring
  have hlogD : log (D : ℝ) = 22 * (ell : ℝ) * B := hcountLog ell hell0
  have hlogD' : log (D' : ℝ) = 22 * (ell' : ℝ) * B' := hcountLog ell' hell'0
  rw [hlogD, hlogD']
  refine ⟨by nlinarith only [hB, hell], ?_⟩
  calc
    22 * (ell' : ℝ) * B' ≤ 22 * ((21 / 10) * (ell : ℝ)) * ((511 / 500) * B) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hscale (by norm_num)) hBscale
        (by dsimp only [B']; positivity) (by positivity)
    _ ≤ (13 / 6) * (22 * (ell : ℝ) * B) := by
      nlinarith only [mul_nonneg hell0.le (show 0 ≤ B by linarith only [hB])]

end Real

section PolynomialFilterDyadicGrowth

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

end PolynomialFilterDyadicGrowth

end PolynomialFilterCounts

section PolynomialFilterLogCount

/-!
## Logarithms of the actual polynomial-filter counts

The base estimate and count calculation are adapted from
`TNLean/MPS/AreaLaw/PolynomialFilterParameters.lean` at commit
`ce9cbdeb7ac5212dcaa3344b7401ce2ca207adcc`. The base estimate keeps
its statement and proof, with a public mathematical name. The count
calculation is separated from the later absorption and suppression
argument, and reuses the existing ceiling bounds.

These scalar estimates support ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041, and Proposition `prop:albootstrap-ld`,
lines 1107–1128. No physical Hamiltonian or suppression bound is assumed.
-/

namespace Real

/-- The logarithm of the actual count base is linear in the logarithmic
scale. Scalar auxiliary for ALVV, t:ais, lines 1010--1024. -/
theorem log_polynomial_filter_base_le (A d g u e : ℝ) (hA : 1 ≤ A)
    (hd : 2 ≤ d) (hg : 0 < g) (hg1 : g ≤ 1)
    (hu : u = 1 + log d + log (1 / g))
    (he : 1 ≤ e) (heup : e ≤ (A + 1) * u ^ 2 / g) :
    log (d * e ^ 2) ≤ (6 + 2 * log (A + 1)) * u := by
  have hd0 : 0 < d := by linarith
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hld : 0 ≤ log d := log_nonneg (by linarith)
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := by linarith
  have he0 : 0 < e := by linarith
  have hAp : 0 < A + 1 := by linarith
  have hla : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hle : log e ≤ log (A + 1) + 2 * log u + log (1 / g) := by
    calc
      log e ≤ log ((A + 1) * u ^ 2 / g) := log_le_log he0 heup
      _ = log (A + 1) + 2 * log u + log (1 / g) := by
        rw [log_div (mul_ne_zero hAp.ne' (pow_ne_zero 2 hu0.ne')) hg.ne',
          log_mul hAp.ne' (pow_ne_zero 2 hu0.ne'), log_pow,
          one_div, log_inv]
        ring
  have hlu : log u ≤ u := log_le_self hu0.le
  have hldg : log d + 2 * log (1 / g) ≤ 2 * u := by rw [hu]; linarith
  have hlaMul : log (A + 1) ≤ log (A + 1) * u := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hla
  calc
    log (d * e ^ 2) = log d + 2 * log e := by
      rw [log_mul hd0.ne' (pow_ne_zero 2 he0.ne'), log_pow]
      norm_num
    _ ≤ log d + 2 * (log (A + 1) + 2 * log u + log (1 / g)) := by
      linarith only [hle]
    _ ≤ 2 * log (A + 1) + 6 * u := by
      linarith only [hlu, hldg]
    _ ≤ (6 + 2 * log (A + 1)) * u := by
      nlinarith only [hlaMul]

/-- The actual natural count has a positive value and explicit logarithmic
bounds for every admissible ceiling constant. The sharper linear-in-degree
bound is retained for the count-suppression argument. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem polynomial_filter_count_bounds (A : ℝ) (d : ℕ) (g : ℝ)
    (hA : 1 ≤ A) (hd : 2 ≤ d) (hg : 0 < g) (hg1 : g ≤ 1) :
    let u : ℝ := 1 + log (d : ℝ) + log (1 / g)
    let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
    let D : ℕ := (d * ell ^ 2) ^ (22 * ell)
    let cA : ℝ := 6 + 2 * log (A + 1)
    A * u ^ 2 / g ≤ (ell : ℝ) ∧
      (ell : ℝ) ≤ (A + 1) * u ^ 2 / g ∧ A ≤ (ell : ℝ) ∧
      0 < (D : ℝ) ∧ log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u ∧
      log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 := by
  intro u ell D cA
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : 0 < (d : ℝ) := by linarith
  have hld : 0 ≤ log (d : ℝ) := log_nonneg (by linarith)
  have hb : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu1 : 1 ≤ u := by dsimp only [u]; linarith
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨hellLower, hellUpper, hellA⟩ :=
    ceil_quadratic_scale_bounds A u g hA hu1 hg hg1
  have hell1 : 1 ≤ (ell : ℝ) := hA.trans hellA
  have hcA0 : 0 ≤ cA := by
    dsimp only [cA]
    have := log_nonneg (show 1 ≤ A + 1 by linarith)
    linarith
  have hbase : log ((d : ℝ) * (ell : ℝ) ^ 2) ≤ cA * u :=
    log_polynomial_filter_base_le A d g u ell hA hdR hg hg1 rfl hell1 hellUpper
  have hDcast : (D : ℝ) = ((d : ℝ) * (ell : ℝ) ^ 2) ^ (22 * ell) := by
    simp only [D, Nat.cast_pow, Nat.cast_mul]
  have hDpos : 0 < (D : ℝ) := by rw [hDcast]; positivity
  have hlogD : log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u := by
    rw [hDcast, log_pow]
    have hmul := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 22 * (ell : ℝ) by positivity)
    push_cast
    nlinarith only [hmul]
  refine ⟨hellLower, hellUpper, hellA, hDpos, hlogD, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hellUpper
    (show 0 ≤ 22 * cA * u by positivity)
  calc
    log (D : ℝ) ≤ 22 * (ell : ℝ) * cA * u := hlogD
    _ ≤ 22 * ((A + 1) * u ^ 2 / g) * cA * u := by nlinarith only [hmul]
    _ = 22 * (A + 1) * cA / g * u ^ 3 := by ring

end Real

end PolynomialFilterLogCount
