/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TypicalTailScales

/-! Uniform budget quantifiers, the sharp logarithmic exponent, and the zero-parameter endpoint. -/

namespace TypicalTailScalesTest

-- Preserve the existing linear-budget statement and all its quantifiers.
example {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ B : ℝ, 0 < B → B ≤ C * (n : ℝ) →
      2 * Real.exp (Real.exp 1 / 2) * Real.exp
        (-((n : ℝ) ^ ((3 : ℝ) / 5) / (32 * Real.sqrt ((1 + θ) * B)))) ≤
      (n : ℝ) ^ (-100 : ℝ) :=
  Entropy.exists_typical_tail_bound_of_linear_budget hθ hC

-- The scale threshold precedes both the scale and every admissible budget.
example {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ B : ℝ, 0 < B →
      B ≤ C * (n : ℝ) * (Real.log (n : ℝ)) ^ 12 →
      2 * Real.exp (Real.exp 1 / 2) * Real.exp
        (-((n : ℝ) ^ ((3 : ℝ) / 5) / (32 * Real.sqrt ((1 + θ) * B)))) ≤
      (n : ℝ) ^ (-100 : ℝ) :=
  Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget hθ hC

-- The source's sharper exponent remains available without an eventual hypothesis.
example {θ C B n : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C) (hB : 0 < B) (hn : 1 < n)
    (hBn : B ≤ C * n * (Real.log n) ^ 12) :
    (32 * Real.sqrt ((1 + θ) * C))⁻¹ * n ^ ((1 : ℝ) / 10) / (Real.log n) ^ 6 ≤
      n ^ ((3 : ℝ) / 5) / (32 * Real.sqrt ((1 + θ) * B)) :=
  Entropy.typicalWidth_div_sqrt_log_pow_twelve_budget_ge hθ hC hB hn hBn

-- The full logarithmic budget, rather than a substituted linear budget, is admissible.
example {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      2 * Real.exp (Real.exp 1 / 2) * Real.exp
        (-((n : ℝ) ^ ((3 : ℝ) / 5) /
          (32 * Real.sqrt ((1 + θ) * (C * (n : ℝ) * (Real.log (n : ℝ)) ^ 12))))) ≤
      (n : ℝ) ^ (-100 : ℝ) := by
  obtain ⟨N, hN, hbound⟩ :=
    Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget hθ hC
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  exact hbound n hn _ (by positivity) le_rfl

-- θ=0 and a positive constant below one are allowed.
example : ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ B : ℝ, 0 < B →
    B ≤ (1 / 2 : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ 12 →
    2 * Real.exp (Real.exp 1 / 2) * Real.exp
      (-((n : ℝ) ^ ((3 : ℝ) / 5) / (32 * Real.sqrt B))) ≤
    (n : ℝ) ^ (-100 : ℝ) := by
  simpa only [add_zero, one_mul] using
    (Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget
      (θ := 0) (C := 1 / 2) (by norm_num) (by norm_num))

end TypicalTailScalesTest
