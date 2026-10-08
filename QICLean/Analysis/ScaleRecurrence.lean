/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Power bounds from a scale recurrence

Let `F` be a nondecreasing function on the positive integers, `M ≥ 2` an integer, and
`λ > M`. If `F (M r) ≤ λ F r + K r` for every `r ≥ 1`, with `K ≥ 0`, then iterating at
`r = 1, M, M², …` gives `F (M^j) ≤ C λ^j`, the inhomogeneous terms forming a geometric
series of ratio `M/λ < 1`. Monotonicity then gives `F r ≤ C' r^{log_M λ}` for all `r ≥ 1`.

## Main results

* `Entropy.le_pow_of_scale_recurrence`: the bound at powers of `M`.
* `Entropy.exists_le_mul_rpow_of_scale_recurrence`: the power bound for all `r ≥ 1`.
* `Entropy.one_lt_log_div_log_lt_two`: the exponent lies in `(1, 2)`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Proposition 3.3
  (`prop:initial-box`), `02-initial.tex`, lines 648–664.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

namespace Entropy

variable {F : ℕ → ℝ} {M : ℕ} {lam K : ℝ}

/-- **Iteration at powers.** Under the scale recurrence,
`F (M^j) ≤ λ^j F 1 + K (λ^j - M^j)/(λ - M)`.
Area-law manuscript, `02-initial.tex`, lines 652–655. -/
theorem le_pow_of_scale_recurrence (hM : 1 ≤ M) (hlam : (M : ℝ) < lam)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r) (j : ℕ) :
    F (M ^ j) ≤ lam ^ j * F 1 + K / (lam - M) * (lam ^ j - (M : ℝ) ^ j) := by
  have hlM : 0 < lam - M := by linarith
  have hlam0 : 0 < lam := lt_of_le_of_lt (by positivity) hlam
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hrec (M ^ j) (Nat.one_le_pow _ _ hM)
    rw [show M * M ^ j = M ^ (j + 1) by ring] at h1
    calc F (M ^ (j + 1)) ≤ lam * F (M ^ j) + K * ((M ^ j : ℕ) : ℝ) := h1
      _ ≤ lam * (lam ^ j * F 1 + K / (lam - M) * (lam ^ j - (M : ℝ) ^ j)) +
          K * ((M ^ j : ℕ) : ℝ) := by gcongr
      _ = lam ^ (j + 1) * F 1 + K / (lam - M) * (lam ^ (j + 1) - (M : ℝ) ^ (j + 1)) := by
          push_cast
          field_simp
          ring

/-- **Power bound from a scale recurrence.** If `F` is nondecreasing, `M ≥ 2`, `λ > M`,
`K ≥ 0` and `F (M r) ≤ λ F r + K r` for every `r ≥ 1`, then there is a constant `C` with
`F r ≤ C r^{log λ / log M}` for every `r ≥ 1`.
Area-law manuscript, proof of Proposition 3.3, `02-initial.tex`, lines 648–664. -/
theorem exists_le_mul_rpow_of_scale_recurrence (hF : Monotone F) (hM : 2 ≤ M)
    (hlam : (M : ℝ) < lam) (hK : 0 ≤ K)
    (hrec : ∀ r, 1 ≤ r → F (M * r) ≤ lam * F r + K * r) :
    ∃ C, ∀ r, 1 ≤ r → F r ≤ C * (r : ℝ) ^ (Real.log lam / Real.log M) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hlM : 0 < lam - M := by linarith
  have hlam1 : 1 < lam := hM1.trans hlam
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  set e := Real.log lam / Real.log M
  have he : 0 ≤ e := div_nonneg (Real.log_pos hlam1).le hlogM.le
  set B := |F 1| + K / (lam - M)
  have hB : 0 ≤ B := by positivity
  -- the bound at powers
  have hpow (j : ℕ) : F (M ^ j) ≤ B * lam ^ j := by
    have h := le_pow_of_scale_recurrence (by omega) hlam hrec j
    have hMj : 0 ≤ K / (lam - M) * (M : ℝ) ^ j := by positivity
    have hF1 := le_abs_self (F 1)
    have hlj : 0 ≤ lam ^ j := by positivity
    nlinarith
  -- `λ^j = (M^j)^e`
  have hrpow (j : ℕ) : lam ^ j = ((M : ℝ) ^ j) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)]
    congr 1
    simp only [e]
    field_simp
  refine ⟨B * (M : ℝ) ^ e, fun r hr ↦ ?_⟩
  set j := Nat.clog M r
  have hrj : r ≤ M ^ j := Nat.le_pow_clog (by omega) r
  have hjr : ((M : ℝ) ^ j) ≤ M * r := by
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · have := Nat.pow_pred_clog_lt_self (b := M) (by omega) h1
      have hj : 1 ≤ j := Nat.clog_pos (by omega) h1
      have h2 : M ^ j = M * M ^ (j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hj]
      have h3 : M ^ j ≤ M * r := by
        rw [h2]; exact Nat.mul_le_mul_left _ this.le
      exact_mod_cast h3
    · have hr1 : r = 1 := le_antisymm h1 hr
      subst hr1
      simp [j]
      linarith
  calc F r ≤ F (M ^ j) := hF hrj
    _ ≤ B * lam ^ j := hpow j
    _ = B * ((M : ℝ) ^ j) ^ e := by rw [hrpow]
    _ ≤ B * ((M : ℝ) * r) ^ e := by gcongr
    _ = B * (M : ℝ) ^ e * (r : ℝ) ^ e := by
        rw [Real.mul_rpow (by positivity) (by positivity)]; ring

/-- If `M < λ < M²` with `M > 1`, the exponent `log_M λ` lies strictly between `1` and `2`,
so `e₀ = log_M λ - 1 ∈ (0, 1)`.
Area-law manuscript, `02-initial.tex`, lines 656–660. -/
theorem one_lt_log_div_log_lt_two {M lam : ℝ} (hM : 1 < M) (h1 : M < lam) (h2 : lam < M ^ 2) :
    1 < Real.log lam / Real.log M ∧ Real.log lam / Real.log M < 2 := by
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hl1 : Real.log M < Real.log lam := Real.log_lt_log (by linarith) h1
  have hl2 : Real.log lam < Real.log (M ^ 2) := Real.log_lt_log (by linarith) h2
  rw [Real.log_pow] at hl2
  push_cast at hl2
  exact ⟨(one_lt_div hlogM).mpr hl1, (div_lt_iff₀ hlogM).mpr (by linarith)⟩

end Entropy
