/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# An eventual numerical threshold for independent-copy tails

For every fixed real coefficient and polynomial degree, the sum of the
inverse-square-root term and the polynomially weighted stretched exponential
is eventually at most one half. This is the numerical step used after the
independent-copy surprisal estimate and the label-observable estimate.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 255–281, `comparator:high-label`, at
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No density matrix, label or concentration hypothesis occurs in this result.
Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:high-label.
Provenance-ID: 8753-qic-iid-tail-threshold-01
Downstream declaration:
Real.eventually_iid_tail_error_le_half
-/

open Filter

namespace Real

/-- A polynomial times the stretched-exponential label tail, together with the
inverse-square-root surprisal tail, is eventually at most one half.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–281,
`comparator:high-label`. The coefficient may be any real number. -/
theorem eventually_iid_tail_error_le_half (V : ℝ) (m : ℕ) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧
      V / Real.sqrt (k : ℝ) + (((k + 1) ^ m : ℕ) : ℝ) *
        Real.exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2) ≤ 1 / 2 := by
  have hpower : Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (3 / 4 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun k : ℕ ↦ (k : ℝ) ^ m *
      exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2)) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (4 * (m : ℝ) / 3) (1 / 2) (by norm_num)).comp hpower
    refine h.congr' ?_
    filter_upwards with k
    dsimp only [Function.comp_apply]
    rw [← rpow_mul (Nat.cast_nonneg k)]
    rw [show (3 / 4 : ℝ) * (4 * (m : ℝ) / 3) = (m : ℝ) by ring, rpow_natCast]
    rw [show -(1 / 2 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ) =
      -((k : ℝ) ^ (3 / 4 : ℝ)) / 2 by ring]
  have hroot : Tendsto (fun k : ℕ ↦ sqrt (k : ℝ)) atTop atTop := by
    simpa only [sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp
        tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun k : ℕ ↦ V / sqrt (k : ℝ) +
      (2 : ℝ) ^ m * ((k : ℝ) ^ m * exp (-((k : ℝ) ^ (3 / 4 : ℝ)) / 2)))
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (hroot.const_div_atTop V).add (hdecay.const_mul ((2 : ℝ) ^ m))
  filter_upwards [eventually_ge_atTop 1,
    hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk hsumk
  have hcoeff : (((k + 1) ^ m : ℕ) : ℝ) ≤ (2 : ℝ) ^ m * (k : ℝ) ^ m := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (show k + 1 ≤ 2 * k by omega)
  refine ⟨hk, le_trans ?_ hsumk.le⟩
  simpa only [mul_assoc] using
    add_le_add_right (mul_le_mul_of_nonneg_right hcoeff (exp_pos _).le) (V / sqrt (k : ℝ))

end Real
