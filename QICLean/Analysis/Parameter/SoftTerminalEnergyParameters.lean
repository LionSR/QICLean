/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Energy budgets for a calibrated terminal family image

The calibrated comparison loss and the exact terminal filtering loss satisfy
the norm-dependent budgets for projected positive energy. The reverse soft
residual also controls the regional middle-only residual. These scalar estimates
support ALVV, arXiv:1602.08828v2, the energy estimate at line 1807; they do not
assert an operator, sampling or runtime conclusion.
-/

namespace Real

/-- The same calibrated profile controls the original-to-target loss and the
exact terminal denominator, with the centered regional norm kept explicit.
Supporting ALVV, arXiv:1602.08828v2, line 1807. -/
theorem soft_terminal_energy_precision_bounds {D M A Delta : ℝ}
    (hD : 2 ≤ D) (hM : 34 ≤ M) (hA0 : 0 ≤ A) (hAM : A ≤ M)
    (hDelta0 : 0 ≤ Delta) (hDelta : Delta ≤ 1 / (D ^ 12 * M ^ 10)) :
    let tau := 1 / (D ^ 24 * M ^ 10)
    tau * M ≤ 1 / 64 ∧
      3 * tau / 200 ≤ 1 / (1024 * (A + 1)) ∧
      Delta / (91 / 100 : ℝ) ^ 2 ≤ 1 / (100 * (A + 1)) := by
  intro tau
  have hD0 : 0 < D := by linarith only [hD]
  have hM1 : 1 ≤ M := by linarith only [hM]
  have hM0 : 0 < M := by linarith only [hM]
  have htau0 : 0 ≤ tau := by dsimp only [tau]; positivity
  have hMpow : M ≤ M ^ 10 := le_self_pow₀ hM1 (by decide)
  have hD24 : (64 : ℝ) ≤ D ^ 24 :=
    (by norm_num : (64 : ℝ) ≤ 2 ^ 24).trans
      (pow_le_pow_left₀ (by norm_num) hD 24)
  have hD12 : (256 : ℝ) ≤ D ^ 12 :=
    (by norm_num : (256 : ℝ) ≤ 2 ^ 12).trans
      (pow_le_pow_left₀ (by norm_num) hD 12)
  have hDen24 : 64 * M ≤ D ^ 24 * M ^ 10 :=
    mul_le_mul hD24 hMpow (by positivity) (by positivity)
  have hDen12 : 256 * M ≤ D ^ 12 * M ^ 10 :=
    mul_le_mul hD12 hMpow (by positivity) (by positivity)
  have htauSmall : tau ≤ 1 / (64 * M) :=
    one_div_le_one_div_of_le (by positivity) hDen24
  have htauM : tau * M ≤ 1 / 64 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 64 * M)).mp htauSmall
    nlinarith only [hh]
  have htauA : tau * (A + 1) ≤ 2 * (tau * M) := by
    have hh := mul_le_mul_of_nonneg_left (by linarith only [hAM, hM1] : A + 1 ≤ 2 * M) htau0
    nlinarith only [hh]
  have hDeltaM : Delta * M ≤ 1 / 256 := by
    have hh := (le_div_iff₀ (by positivity : 0 < D ^ 12 * M ^ 10)).mp hDelta
    have hmul := mul_le_mul_of_nonneg_left hDen12 hDelta0
    nlinarith only [hh, hmul]
  have hDeltaA : Delta * (A + 1) ≤ 2 * (Delta * M) := by
    have hh := mul_le_mul_of_nonneg_left (by linarith only [hAM, hM1] : A + 1 ≤ 2 * M) hDelta0
    nlinarith only [hh]
  refine ⟨htauM, ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < 1024 * (A + 1))).mpr
    nlinarith only [htauM, htauA]
  · apply (le_div_iff₀ (by positivity : 0 < 100 * (A + 1))).mpr
    norm_num [div_eq_mul_inv]
    nlinarith only [hDeltaM, hDeltaA]

/-- The reverse calibrated soft tail controls the middle-only residual.
Only the nonnegative gap parameter and its norm scale enter this comparison;
there is no upper bound on the gap. Supporting ALVV,
arXiv:1602.08828v2, the energy estimate at line 1807. -/
theorem soft_terminal_regional_residual_le {g M tau t T : ℝ} {m : ℕ}
    (hg : 0 ≤ g) (hgM : g ≤ M) (htau : 0 ≤ tau) (htauM : tau * M ≤ 1)
    (htail : 3 * (32 * exp (-(T - 156 - 2 * g) / 8) +
      (t / (m : ℝ)) * (T / t) ^ m) ≤ tau * g / 1000000) :
    32 * exp (-(T - 48) / 8) + (t / (m : ℝ)) * (T / t) ^ m ≤ 1 / 16 := by
  have hexp : exp (-(T - 48) / 8) ≤ exp (-(T - 156 - 2 * g) / 8) :=
    exp_le_exp.mpr (by linarith only [hg])
  have hcompare := add_le_add_right (mul_le_mul_of_nonneg_left hexp
    (by norm_num : (0 : ℝ) ≤ 32)) ((t / (m : ℝ)) * (T / t) ^ m)
  have hnum : tau * g ≤ 1 :=
    (mul_le_mul_of_nonneg_left hgM htau).trans htauM
  linarith only [htail, hcompare, hnum]

/-- The centered regional norm is at most the common soft norm ceiling,
which also dominates three times the truncation scale. Supporting ALVV,
arXiv:1602.08828v2, the regional energy estimate at line 1807. -/
theorem soft_terminal_regional_norm_bounds {t ell : ℝ} {m : ℕ}
    (ht : 0 ≤ t) (hell : 0 ≤ ell) (hm : 1 ≤ m) :
    let A := t * (1 + log (m : ℝ)) + 4 * ell + 14
    let M := 3 * t * (1 + log (m : ℝ)) + 4 * ell + 34
    0 ≤ A ∧ A ≤ M ∧ 3 * t ≤ M ∧ 34 ≤ M := by
  have hlog : 0 ≤ log (m : ℝ) := log_nonneg (by exact_mod_cast hm)
  have hprod := mul_nonneg ht hlog
  dsimp only
  constructor
  · positivity
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [hprod, ht, hell]

end Real
