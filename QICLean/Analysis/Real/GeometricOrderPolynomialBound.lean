/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

/-!
# Polynomial bounds at a logarithmic geometric-tail order

For fixed positive approximation budgets and a fixed geometric ratio in
`(0,1)`, the explicit geometric-tail order grows at most logarithmically
with the length. A fixed power of its polynomial-exponential bond expression
therefore has a polynomial bound whose coefficient and natural degree are
chosen before that length.

This is a numerical auxiliary for the soft heat expansion in ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff` and `t:aisefficient`, lines
1262–1268 and 1373–1420. The filter degree is fixed before the length.
No estimate for a degree growing with the length, or running-time bound,
is asserted.

## Main results

* `Real.exponential_geometric_tail_order`: an explicit order for an exponential geometric tail.
-/

section GeometricOrderPolynomialBound

namespace Real

private theorem geometric_tail_order_le_affine_log
    (b W xi : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (_hW : 0 < W) (_hxi : 0 < xi)
    (N : ℕ) :
    let d := -log b
    let L := log (log (1 + xi / W))
    let a0 := 2 + |L| / d
    let a1 := 2 / d
    let r := max 1 ⌈(log (max 1 ((N : ℝ) ^ 2)) - L) / d⌉₊
    (r : ℝ) ≤ a0 + a1 * log ((N : ℝ) + 1) := by
  intro d L a0 a1 r
  have hd : 0 < d := neg_pos.mpr (log_neg hb0 hb1)
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hX : 1 ≤ (N : ℝ) + 1 := by linarith only [hN]
  have hlogX : 0 ≤ log ((N : ℝ) + 1) := log_nonneg hX
  have hA : 0 < max 1 ((N : ℝ) ^ 2) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlogA : log (max 1 ((N : ℝ) ^ 2)) ≤ 2 * log ((N : ℝ) + 1) := by
    calc
      log (max 1 ((N : ℝ) ^ 2)) ≤ log (((N : ℝ) + 1) ^ 2) :=
        log_le_log hA (max_le (by nlinarith only [hN]) (by nlinarith only [hN]))
      _ = 2 * log ((N : ℝ) + 1) := by rw [log_pow]; norm_num
  have hquot : (log (max 1 ((N : ℝ) ^ 2)) - L) / d ≤
      |L| / d + a1 * log ((N : ℝ) + 1) := by
    calc
      (log (max 1 ((N : ℝ) ^ 2)) - L) / d ≤
          (2 * log ((N : ℝ) + 1) + |L|) / d :=
        div_le_div_of_nonneg_right (by linarith only [hlogA, neg_le_abs L]) hd.le
      _ = |L| / d + a1 * log ((N : ℝ) + 1) := by dsimp only [a1]; ring
  have ha0 : 2 ≤ a0 := by
    have h : 0 ≤ |L| / d := by positivity
    dsimp only [a0]
    linarith only [h]
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hceil : (⌈(log (max 1 ((N : ℝ) ^ 2)) - L) / d⌉₊ : ℝ) ≤
      a0 + a1 * log ((N : ℝ) + 1) := by
    by_cases hx : 0 ≤ (log (max 1 ((N : ℝ) ^ 2)) - L) / d
    · have hc := (Nat.ceil_lt_add_one hx).le
      dsimp only [a0]
      linarith only [hc, hquot]
    · rw [Nat.ceil_eq_zero.mpr (le_of_not_ge hx), Nat.cast_zero]
      nlinarith only [ha0, mul_nonneg ha1 hlogX]
  dsimp only [r]
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by nlinarith only [ha0, mul_nonneg ha1 hlogX]) hceil

/-- Fixed powers of the bond expression at the explicit geometric-tail order
are bounded by one natural polynomial, uniformly in the length, including
zero length. This numerical auxiliary supports the soft approximation in
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff` and `t:aisefficient`,
lines 1262–1268 and 1373–1420. All parameters except the length are fixed
before the coefficient and degree are selected. -/
theorem exists_geometric_order_polynomial_bound
    (b W xi : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hW : 0 < W) (hxi : 0 < xi)
    (q : ℕ) (hq : 1 ≤ q) (s k : ℕ) :
    ∃ C p : ℕ, 1 ≤ C ∧ ∀ N : ℕ,
      let r := max 1 ⌈(log (max 1 ((N : ℝ) ^ 2)) -
        log (log (1 + xi / W))) / (-log b)⌉₊
      (2 * s * r ^ 2 * q ^ r) ^ (2 * k) ≤ C * (N + 1) ^ p := by
  let d := -log b
  let L := log (log (1 + xi / W))
  let a0 := 2 + |L| / d
  let a1 := 2 / d
  let p0 := ⌈a1 * log (q : ℝ)⌉₊
  let K := 2 * (s : ℝ) * (a0 + a1) ^ 2 * exp (a0 * log (q : ℝ))
  let C := max 1 ⌈K ^ (2 * k)⌉₊
  let p := (p0 + 2) * (2 * k)
  have hd : 0 < d := neg_pos.mpr (log_neg hb0 hb1)
  have ha0 : 0 ≤ a0 := by dsimp only [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hC : K ^ (2 * k) ≤ (C : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  refine ⟨C, p, le_max_left _ _, ?_⟩
  intro N r
  let X := (N : ℝ) + 1
  have hX : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hr : (r : ℝ) ≤ a0 + a1 * log X :=
    geometric_tail_order_le_affine_log b W xi hb0 hb1 hW hxi N
  have hlogXle : log X ≤ X := (log_le_sub_one_of_pos hX0).trans (by linarith)
  have hrlinear : (r : ℝ) ≤ (a0 + a1) * X := by
    have h0 := mul_le_mul_of_nonneg_left hX ha0
    have h1 := mul_le_mul_of_nonneg_left hlogXle ha1
    nlinarith only [hr, h0, h1]
  have hrsq : (r : ℝ) ^ 2 ≤ (a0 + a1) ^ 2 * X ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg r) hrlinear 2
  have hqpow : (q : ℝ) ^ r ≤ exp (a0 * log (q : ℝ)) * X ^ p0 := by
    calc
      (q : ℝ) ^ r = exp ((r : ℝ) * log (q : ℝ)) := by
        rw [exp_nat_mul, exp_log hq0]
      _ ≤ exp ((a0 + a1 * log X) * log (q : ℝ)) :=
        exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr hlogq)
      _ = exp (a0 * log (q : ℝ)) * X ^ (a1 * log (q : ℝ)) := by
        rw [rpow_def_of_pos hX0, ← exp_add]
        congr 1
        ring
      _ ≤ exp (a0 * log (q : ℝ)) * X ^ p0 := by
        simpa only [rpow_natCast] using mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_exponent_le hX (Nat.le_ceil (a1 * log (q : ℝ))))
          (exp_pos (a0 * log (q : ℝ))).le
  have hbase : ((2 * s * r ^ 2 * q ^ r : ℕ) : ℝ) ≤ K * X ^ (p0 + 2) := by
    have hprod := mul_le_mul hrsq hqpow (by positivity) (by positivity)
    have hprod' := mul_le_mul_of_nonneg_left hprod
      (by positivity : 0 ≤ 2 * (s : ℝ))
    push_cast
    calc
      2 * (s : ℝ) * (r : ℝ) ^ 2 * (q : ℝ) ^ r =
          2 * (s : ℝ) * ((r : ℝ) ^ 2 * (q : ℝ) ^ r) := by ring
      _ ≤ 2 * (s : ℝ) * (((a0 + a1) ^ 2 * X ^ 2) *
          (exp (a0 * log (q : ℝ)) * X ^ p0)) := hprod'
      _ = K * X ^ (p0 + 2) := by dsimp only [K]; rw [pow_add]; ring
  have hfinal : (((2 * s * r ^ 2 * q ^ r) ^ (2 * k) : ℕ) : ℝ) ≤
      (C : ℝ) * X ^ p := by
    calc
      (((2 * s * r ^ 2 * q ^ r) ^ (2 * k) : ℕ) : ℝ) ≤
          (K * X ^ (p0 + 2)) ^ (2 * k) := by
        simpa only [Nat.cast_pow] using
          pow_le_pow_left₀ (Nat.cast_nonneg _) hbase (2 * k)
      _ = K ^ (2 * k) * X ^ p := by rw [mul_pow, ← pow_mul]
      _ ≤ (C : ℝ) * X ^ p := mul_le_mul_of_nonneg_right hC (pow_nonneg hX0.le _)
  have hnat : (((2 * s * r ^ 2 * q ^ r) ^ (2 * k) : ℕ) : ℝ) ≤
      ((C * (N + 1) ^ p : ℕ) : ℝ) := by
    simpa only [X, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hfinal
  exact Nat.cast_le.mp hnat

end Real

section GeometricDecay

/-!
# Exponential bounds for complete-window geometric decay

A geometric factor counted in complete fixed-width windows is bounded by an exponential
in the original interval length. The lower bound on the geometric base controls the
one-window rounding factor uniformly.
-/

namespace Real

/-- For a base in `[1/2,1)`, counting only complete windows loses at most a factor two
relative to the exponential rate in the full interval length. -/
theorem pow_nat_div_le_two_mul_exp (s n : ℕ) (hs : 0 < s) (ρ : ℝ)
    (hρhalf : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) :
    ρ ^ (n / s) ≤ 2 * Real.exp (-((-Real.log ρ / s) * n)) := by
  have hρ0 : 0 < ρ := by linarith
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have ht : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ0 hρ1)
  have hn : (n : ℝ) ≤ (n / s : ℕ) * s + s := by
    have hd := Nat.div_add_mod n s
    rw [Nat.mul_comm s (n / s)] at hd
    have hm := Nat.mod_lt n hs
    exact_mod_cast (show n ≤ n / s * s + s by omega)
  have hf : (n : ℝ) / s ≤ (n / s : ℕ) + 1 := by
    apply (div_le_iff₀ hsR).mpr
    nlinarith
  have hb := mul_le_mul_of_nonneg_left hf ht.le
  have hinv : ρ⁻¹ ≤ 2 := by
    simpa only [one_div] using (one_div_le hρ0 two_pos).mpr hρhalf
  calc ρ ^ (n / s) = Real.exp ((n / s : ℕ) * Real.log ρ) := by
        rw [Real.exp_nat_mul, Real.exp_log hρ0]
    _ ≤ Real.exp (-Real.log ρ + -((-Real.log ρ / s) * n)) := by
        apply Real.exp_le_exp.mpr
        calc (n / s : ℕ) * Real.log ρ = -((-Real.log ρ) * (n / s : ℕ)) := by ring
          _ ≤ -Real.log ρ - (-Real.log ρ) * ((n : ℝ) / s) := by nlinarith
          _ = _ := by ring
    _ = ρ⁻¹ * Real.exp (-((-Real.log ρ / s) * n)) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hρ0]
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le

end Real

end GeometricDecay

end GeometricOrderPolynomialBound

section ExponentialGeometricTailOrder

/-!
## An explicit order for an exponential geometric tail

A logarithmic ceiling chooses an actual truncation order from a positive accuracy budget.
Supporting the corrected cluster approximation used in ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. This scalar choice makes no running-time assertion.
-/

namespace Real

/-- An explicit positive order makes a weighted exponential geometric tail smaller than the
prescribed error. This is an auxiliary parameter choice for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268, with the corrected cluster estimate. -/
lemma exponential_geometric_tail_order (N W b xi : ℝ) (hW : 0 < W)
    (hb0 : 0 < b) (hb1 : b < 1) (hxi : 0 < xi) :
    let r := max 1 ⌈(log (max 1 (N ^ 2)) - log (log (1 + xi / W))) / (-log b)⌉₊
    0 < r ∧ W * (exp (N ^ 2 * b ^ r) - 1) ≤ xi := by
  intro r
  let A := max 1 (N ^ 2)
  let d := log (1 + xi / W)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hd : 0 < d := log_pos (by linarith [div_pos hxi hW])
  have hb : log b < 0 := log_neg hb0 hb1
  have hr : (log A - log d) / (-log b) ≤ (r : ℝ) := by
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have hlog : log A + (r : ℝ) * log b ≤ log d := by
    have hmul := (div_le_iff₀ (neg_pos.mpr hb)).mp hr
    linarith
  have hp : A * b ^ r ≤ d := by
    have he := exp_le_exp.mpr hlog
    rw [exp_add, exp_log hA, exp_nat_mul, exp_log hb0, exp_log hd] at he
    exact he
  have hNd : N ^ 2 * b ^ r ≤ d :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hb0.le _)).trans hp
  have he : exp (N ^ 2 * b ^ r) - 1 ≤ xi / W := by
    have h := exp_le_exp.mpr hNd
    rw [exp_log (by positivity : 0 < 1 + xi / W)] at h
    linarith
  refine ⟨lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  exact (mul_le_mul_of_nonneg_left he hW.le).trans_eq (by field_simp)

end Real

end ExponentialGeometricTailOrder
