/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Wendel's inequalities for ratios of Gamma values

For `x > 0` and `0 ≤ s ≤ 1`, log-convexity of the Gamma function gives

`x (x + s)^(s - 1) ≤ Γ(x + s) / Γ(x) ≤ x^s`,

the inequalities of Wendel (1948). For `x ≥ 1` they give `|Γ(x + s)/Γ(x) - x^s| ≤ s`.
These are the gamma-ratio estimates used for the marked ratios of the replica metrics in the
area-law paper (*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 410–413: "Gamma ratios give `r_{λ,i} ≍ ((l_i + 1)/k)^t`").

## Main declarations

* `Real.Gamma_add_le_rpow_mul_Gamma` — `Γ(x + s) ≤ x^s Γ(x)`.
* `Real.mul_Gamma_le_rpow_mul_Gamma_add` — `x Γ(x) ≤ (x + s)^(1 - s) Γ(x + s)`.
* `Real.rpow_sub_le_Gamma_add_div_Gamma` — `x^s - s ≤ Γ(x + s)/Γ(x)` for `x ≥ 1`.
-/

open Real

namespace Real

variable {x s : ℝ}

/-- **Wendel's upper inequality**: `Γ(x + s) ≤ x^s Γ(x)` for `x > 0` and `0 ≤ s ≤ 1`. -/
theorem Gamma_add_le_rpow_mul_Gamma (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Gamma (x + s) ≤ x ^ s * Gamma x := by
  have hG := Gamma_pos_of_pos hx
  rcases hs0.eq_or_lt with rfl | hs0
  · simp
  rcases hs1.eq_or_lt with rfl | hs1
  · rw [rpow_one, Gamma_add_one hx.ne']
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1) (a := 1 - s)
    (b := s) hx (by linarith) (by linarith) hs0 (by ring)
  have he : (1 - s) * x + s * (x + 1) = x + s := by ring
  rw [he, Gamma_add_one hx.ne', mul_rpow hx.le hG.le] at h
  calc Gamma (x + s) ≤ Gamma x ^ (1 - s) * (x ^ s * Gamma x ^ s) := h
    _ = x ^ s * (Gamma x ^ (1 - s) * Gamma x ^ s) := by ring
    _ = x ^ s * Gamma x := by rw [← rpow_add hG]; simp

/-- **Wendel's lower inequality**: `x Γ(x) ≤ (x + s)^(1 - s) Γ(x + s)` for `x > 0` and
`0 ≤ s ≤ 1`. -/
theorem mul_Gamma_le_rpow_mul_Gamma_add (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x * Gamma x ≤ (x + s) ^ (1 - s) * Gamma (x + s) := by
  rcases hs0.eq_or_lt with rfl | hs0
  · simp
  rcases hs1.eq_or_lt with rfl | hs1
  · rw [sub_self, rpow_zero, one_mul, Gamma_add_one hx.ne']
  have hxs : 0 < x + s := by linarith
  have hG := Gamma_pos_of_pos hxs
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + s) (t := x + s + 1)
    (a := s) (b := 1 - s) hxs (by linarith) hs0 (by linarith) (by ring)
  have he : s * (x + s) + (1 - s) * (x + s + 1) = x + 1 := by ring
  rw [he, Gamma_add_one hx.ne', Gamma_add_one hxs.ne', mul_rpow hxs.le hG.le] at h
  calc x * Gamma x ≤ Gamma (x + s) ^ s * ((x + s) ^ (1 - s) * Gamma (x + s) ^ (1 - s)) := h
    _ = (x + s) ^ (1 - s) * (Gamma (x + s) ^ s * Gamma (x + s) ^ (1 - s)) := by ring
    _ = (x + s) ^ (1 - s) * Gamma (x + s) := by rw [← rpow_add hG]; simp

/-- Wendel's upper inequality in ratio form: `Γ(x + s)/Γ(x) ≤ x^s`. -/
theorem Gamma_add_div_Gamma_le_rpow (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Gamma (x + s) / Gamma x ≤ x ^ s :=
  (div_le_iff₀ (Gamma_pos_of_pos hx)).mpr (Gamma_add_le_rpow_mul_Gamma hx hs0 hs1)

/-- Wendel's lower inequality in ratio form: `x / (x + s)^(1 - s) ≤ Γ(x + s)/Γ(x)`. -/
theorem div_rpow_le_Gamma_add_div_Gamma (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x / (x + s) ^ (1 - s) ≤ Gamma (x + s) / Gamma x := by
  have hxs : 0 < (x + s) ^ (1 - s) := rpow_pos_of_pos (by linarith) _
  rw [div_le_div_iff₀ hxs (Gamma_pos_of_pos hx)]
  linarith [mul_Gamma_le_rpow_mul_Gamma_add hx hs0 hs1]

/-- For `x ≥ 1` and `0 ≤ s ≤ 1`, `x^s - s ≤ Γ(x + s)/Γ(x)`. Together with
`Gamma_add_div_Gamma_le_rpow`, `|Γ(x + s)/Γ(x) - x^s| ≤ s`. -/
theorem rpow_sub_le_Gamma_add_div_Gamma (hx : 1 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ s - s ≤ Gamma (x + s) / Gamma x := by
  have hx0 : 0 < x := by linarith
  have hxs : 0 < x + s := by linarith
  refine le_trans ?_ (div_rpow_le_Gamma_add_div_Gamma hx0 hs0 hs1)
  -- `(x + s)^(1 - s) = (x + s) / (x + s)^s ≤ (x + s) / x^s`.
  have hpow : (x + s) ^ (1 - s) = (x + s) / (x + s) ^ s := by
    rw [rpow_sub hxs, rpow_one]
  have hxs_pow : x ^ s ≤ (x + s) ^ s := rpow_le_rpow hx0.le (by linarith) hs0
  have hxpow_pos : 0 < x ^ s := rpow_pos_of_pos hx0 _
  have hxpow_le : x ^ s ≤ x := by
    simpa using rpow_le_rpow_of_exponent_le hx hs1
  rw [hpow, div_div_eq_mul_div, le_div_iff₀ hxs]
  -- `(x^s - s)(x + s) ≤ x x^s ≤ x (x + s)^s`.
  nlinarith [mul_le_mul_of_nonneg_left hxs_pow hx0.le]

end Real
