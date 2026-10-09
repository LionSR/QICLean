/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Typical spectral widths for a linear cut budget

The exponential marginal-tail estimate gives an inverse polynomial error at
width `n^(3/5)` whenever its cut budget is bounded by a fixed multiple of `n`.
The threshold is uniform over all budgets satisfying that bound. The proof
uses Mathlib's comparison of exponential decay with real powers.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 39–55, and Lemma 3.1,
`02-initial.tex`, lines 64–69, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This auxiliary numerical result derives neither the geometric budget bound
nor the spectral tail estimate for an actual Hamiltonian.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:typical-set.
Additional manuscript passage: build/sections/02-initial.tex, Lemma 3.1 (lem:tail).
-/

open Filter Asymptotics

namespace Entropy

private theorem stretchedExp_isLittleO {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (s : ℝ) :
    (fun x : ℝ ↦ Real.exp (-c * x ^ p)) =o[atTop] (fun x : ℝ ↦ x ^ s) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (s / p)).comp_tendsto
    (tendsto_rpow_atTop hp)
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Function.comp_apply, ← Real.rpow_mul hx]
  congr 1
  field_simp

private theorem eventually_stretchedExp_le_rpow {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (A s : ℝ) :
    ∀ᶠ x : ℝ in atTop, A * Real.exp (-c * x ^ p) ≤ x ^ s := by
  have h := (stretchedExp_isLittleO hp hc s).const_mul_left A
  filter_upwards [h.bound zero_lt_one, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 s), one_mul]
    using (le_abs_self (A * Real.exp (-c * x ^ p))).trans hx

private theorem typicalWidth_div_sqrt_budget_ge {θ C B n : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C) (hB : 0 < B)
    (hn : 0 < n) (hBn : B ≤ C * n) :
    (32 * Real.sqrt ((1 + θ) * C))⁻¹ * n ^ ((1 : ℝ) / 10) ≤
      n ^ ((3 : ℝ) / 5) / (32 * Real.sqrt ((1 + θ) * B)) := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hdenom : 32 * Real.sqrt ((1 + θ) * B) ≤
      (32 * Real.sqrt ((1 + θ) * C)) * Real.sqrt n := by
    calc
      _ ≤ 32 * Real.sqrt ((1 + θ) * (C * n)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left hBn hθ1.le)) (by norm_num)
      _ = _ := by rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hθ1.le hC.le), mul_assoc]
  have hsplit : n ^ ((3 : ℝ) / 5) = n ^ ((1 : ℝ) / 10) * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
    norm_num
  have hdpos : 0 < 32 * Real.sqrt ((1 + θ) * B) := by positivity
  calc
    _ = n ^ ((3 : ℝ) / 5) / ((32 * Real.sqrt ((1 + θ) * C)) * Real.sqrt n) := by
      rw [hsplit]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le _) hdpos hdenom

/-- The marginal-tail expression at width `n^(3/5)` is at most `n^(-100)` for
all sufficiently large natural scales, uniformly over `0 < B ≤ C * n`.
The threshold depends only on `θ` and `C`. This is the numerical implication
used in OpenAI's area-law manuscript, `07-comparators.tex`, lines 39–55,
`comparator:typical-set`, following Lemma 3.1 (`lem:tail`),
`02-initial.tex`, lines 64–69. The geometric budget bound and the actual
Hamiltonian tail estimate remain separate hypotheses in their applications. -/
theorem exists_typical_tail_bound_of_linear_budget {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ B : ℝ, 0 < B → B ≤ C * (n : ℝ) →
      2 * Real.exp (Real.exp 1 / 2) * Real.exp
        (-((n : ℝ) ^ ((3 : ℝ) / 5) / (32 * Real.sqrt ((1 + θ) * B)))) ≤
      (n : ℝ) ^ (-100 : ℝ) := by
  let c := (32 * Real.sqrt ((1 + θ) * C))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hr := eventually_stretchedExp_le_rpow (by norm_num : 0 < (1 : ℝ) / 10) hc
    (2 * Real.exp (Real.exp 1 / 2)) (-100)
  have he : ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (Real.exp 1 / 2) * Real.exp (-c * (n : ℝ) ^ ((1 : ℝ) / 10)) ≤
        (n : ℝ) ^ (-100 : ℝ) := tendsto_natCast_atTop_atTop.eventually hr
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn B hB hBn
  have hn0 : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hcoef := typicalWidth_div_sqrt_budget_ge hθ hC hB hnr hBn
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hcoef)
  calc
    _ ≤ 2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * Real.exp (Real.exp 1 / 2) * Real.exp (-c * (n : ℝ) ^ ((1 : ℝ) / 10)) := by
      rw [neg_mul]
    _ ≤ _ := hN n ((le_max_left _ _).trans hn)

end Entropy
