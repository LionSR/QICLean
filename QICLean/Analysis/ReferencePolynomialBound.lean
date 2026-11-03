/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial consequences of logarithmic reference bounds

The reference spaces used in ALVV, arXiv:1602.08828v2, proof of `t:alg1`,
lines 1801–1817, have explicit logarithmic bond bounds. The sublinear term
in the accuracy logarithm is bounded linearly here, so that the dependence
on the chain length, ground multiplicity and inverse accuracy can be made
polynomial when the physical local dimension and gap are fixed.
-/

namespace Real

/-- A linear upper bound for the sublinear accuracy term in the reference
bond estimate. This is an auxiliary numerical estimate for ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1817. -/
theorem rpow_three_quarters_mul_one_add_log_le {b : ℝ} (hb : 1 ≤ b) :
    b ^ (3 / 4 : ℝ) * (1 + log b) ≤ 5 * b := by
  have hb0 : 0 < b := by linarith
  have hlog : log b ≤ 4 * b ^ (1 / 4 : ℝ) := by
    have hh := log_le_rpow_div hb0.le (by norm_num : (0 : ℝ) < 1 / 4)
    norm_num at hh
    nlinarith only [hh]
  have hpow : b ^ (3 / 4 : ℝ) ≤ b := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hb (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hprod : b ^ (3 / 4 : ℝ) * b ^ (1 / 4 : ℝ) = b := by
    rw [← rpow_add hb0]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hlog (rpow_nonneg hb0.le (3 / 4 : ℝ))
  nlinarith only [hpow, hprod, hscaled]

/-- The logarithmic reference-bond expression is at most linear in its
accuracy logarithm. Auxiliary to ALVV, arXiv:1602.08828v2, proof of
`t:alg1`, lines 1801–1817. -/
theorem reference_log_bound_le_linear {a0 a1 b : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hb : 1 ≤ b) :
    (a0 + a1 * b ^ (3 / 4 : ℝ)) * (1 + log b) ≤ (a0 + 5 * a1) * b := by
  have hbasic : 1 + log b ≤ b := by
    linarith [log_le_sub_one_of_pos (by linarith : 0 < b)]
  calc
    _ = a0 * (1 + log b) + a1 * (b ^ (3 / 4 : ℝ) * (1 + log b)) := by ring
    _ ≤ a0 * b + a1 * (5 * b) := add_le_add
      (mul_le_mul_of_nonneg_left hbasic ha0)
      (mul_le_mul_of_nonneg_left (rpow_three_quarters_mul_one_add_log_le hb) ha1)
    _ = _ := by ring

/-- Exponentiating a linear logarithmic bound gives a power bound with an
explicit constant. This supports the reference-bond estimates in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1817. -/
theorem le_exp_mul_rpow_of_log_le {B X p b : ℝ} (hB : 0 < B) (hX : 0 < X)
    (h : log B ≤ p * (b + log X)) : B ≤ exp (p * b) * X ^ p := by
  rw [← exp_log hB, rpow_def_of_pos hX, ← exp_add, exp_le_exp]
  nlinarith only [h]

/-- The inverse refinement and reference accuracies are explicit polynomial
expressions in the norm-to-gap ratio and inverse requested error. Auxiliary
to the parameter choices in ALVV, arXiv:1602.08828v2, final refinement,
lines 1801–1817. -/
theorem viable_refinement_inverse_parameters {A gamma eta : ℝ}
    (hA : 0 < A) (hgamma : 0 < gamma) (heta : 0 < eta) :
    let c := gamma / A
    let rho := eta * gamma / (2 * A + eta * gamma)
    let epsilon := c ^ 2 * rho / 32768
    1 / (c * rho) = 2 * (A / gamma) ^ 2 / eta + A / gamma ∧
      1 / epsilon = 65536 * (A / gamma) ^ 3 / eta + 32768 * (A / gamma) ^ 2 := by
  intro c rho epsilon
  have hden : 0 < 2 * A + eta * gamma := by positivity
  constructor <;> dsimp only [c, rho, epsilon]
  all_goals field_simp [hA.ne', hgamma.ne', heta.ne', hden.ne']
  ring

/-- Polynomial upper bounds for the inverse scalar refinement parameters.
Here `x` is the norm-to-gap ratio and `y` the inverse requested error.
Auxiliary to ALVV, arXiv:1602.08828v2, final refinement, lines 1801–1817. -/
theorem refinement_cost_polynomial_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * x ^ 2 * y + x ≤ 3 * (1 + x) ^ 2 * (1 + y) ∧
      65536 * x ^ 3 * y + 32768 * x ^ 2 ≤ 98304 * (1 + x) ^ 3 * (1 + y) := by
  have hxy := mul_nonneg hx hy
  have hx2y := mul_nonneg (sq_nonneg x) hy
  have hx3 := pow_nonneg hx 3
  have hx3y := mul_nonneg hx3 hy
  constructor
  all_goals nlinarith only [hx, hy, hxy, hx2y, hx3, hx3y, sq_nonneg x]

/-- An integer power controls the complete logarithmic reference-bond
profile. The constant and exponent are independent of the accuracy factor.
Auxiliary to ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1817. -/
theorem reference_bound_le_nat_power {K a0 a1 b0 B X : ℝ}
    (hK : 0 ≤ K) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hb0 : 1 ≤ b0)
    (hB : 0 < B) (hX : 1 ≤ X)
    (h : log B ≤ K * (a0 + a1 * (b0 + log X) ^ (3 / 4 : ℝ)) *
      (1 + log (b0 + log X))) :
    B ≤ exp (K * (a0 + 5 * a1) * b0) * X ^ Nat.ceil (K * (a0 + 5 * a1)) := by
  have hb : 1 ≤ b0 + log X := hb0.trans (le_add_of_nonneg_right (log_nonneg hX))
  have hlinear := mul_le_mul_of_nonneg_left (reference_log_bound_le_linear ha0 ha1 hb) hK
  have hlog : log B ≤ (K * (a0 + 5 * a1)) * (b0 + log X) := by
    nlinarith only [h, hlinear]
  refine (le_exp_mul_rpow_of_log_le hB (by linarith : 0 < X) hlog).trans ?_
  simpa only [rpow_natCast] using mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_exponent_le hX (Nat.le_ceil (K * (a0 + 5 * a1))))
    (exp_pos (K * (a0 + 5 * a1) * b0)).le

/-- The inverse refinement errors grow at most cubically and quartically
in a common upper bound for the spectral width and inverse requested error.
The constants depend only on the lower spectral gap. Auxiliary to ALVV,
arXiv:1602.08828v2, final refinement, lines 1801–1817. -/
theorem viable_refinement_costs_le_polynomial {A gamma eta Z : ℝ}
    (hA : 0 < A) (hgamma : 0 < gamma) (heta : 0 < eta)
    (hZ : 1 ≤ Z) (hAZ : A ≤ Z) (hetaZ : 1 / eta ≤ Z) :
    let c := gamma / A
    let rho := eta * gamma / (2 * A + eta * gamma)
    let epsilon := c ^ 2 * rho / 32768
    1 / (c * rho) ≤ 6 * (1 + 1 / gamma) ^ 2 * Z ^ 3 ∧
      1 / epsilon ≤ 196608 * (1 + 1 / gamma) ^ 3 * Z ^ 4 := by
  intro c rho epsilon
  have hxb : 1 + A / gamma ≤ (1 + 1 / gamma) * Z := by
    simpa only [div_eq_mul_inv, add_mul, mul_add, one_mul, mul_one, mul_comm] using
      add_le_add hZ (div_le_div_of_nonneg_right hAZ hgamma.le)
  have hyb : 1 + 1 / eta ≤ 2 * Z := by linarith only [hetaZ, hZ]
  rw [(viable_refinement_inverse_parameters hA hgamma heta).1,
    (viable_refinement_inverse_parameters hA hgamma heta).2]
  obtain ⟨h2, h3⟩ := refinement_cost_polynomial_bounds
    (div_pos hA hgamma).le (one_div_pos.mpr heta).le
  constructor
  · calc
      _ ≤ 3 * (1 + A / gamma) ^ 2 * (1 + 1 / eta) := by
        simpa only [div_eq_mul_inv, one_mul] using h2
      _ ≤ 3 * ((1 + 1 / gamma) * Z) ^ 2 * (2 * Z) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 98304 * (1 + A / gamma) ^ 3 * (1 + 1 / eta) := by
        simpa only [div_eq_mul_inv, one_mul] using h3
      _ ≤ 98304 * ((1 + 1 / gamma) * Z) ^ 3 * (2 * Z) := by gcongr
      _ = _ := by ring

end Real
