/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Iterating a normalized filter with small trimming errors

ALVV, arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640, repeats filtering
and collective trimming before the final spectral extraction. The estimates
below give a stable numerical recurrence for these two operations.
-/

namespace Real

/-- If a filter contracts squared norms by `1-c`, its normalized error contracts by
at least `1-c/2` while the initial error is at most one half. This auxiliary
estimate refines ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1813. -/
theorem normalized_filter_error_le {c δ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    (1 - c) * δ / (1 - δ + (1 - c) * δ) ≤ (1 - c / 2) * δ := by
  have hd : 0 < 1 - δ + (1 - c) * δ := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-c) hδ0]
  rw [div_le_iff₀ hd]
  have hh : 0 ≤ c * δ * (1 - 2 * δ + c * δ) := by
    apply mul_nonneg (mul_nonneg hc.le hδ0)
    nlinarith [mul_nonneg hc.le hδ0]
  nlinarith

/-- A quadratic trimming budget gives a linear error recurrence after normalized
filtering. This auxiliary estimate controls the repeated operations in ALVV,
arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640. -/
theorem filter_trim_error_le {c δ ε η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hη : 0 ≤ η)
    (hε : ε ≤ c ^ 2 * η / 40) :
    (1 + c / 4) * ((1 - c) * δ / (1 - δ + (1 - c) * δ)) +
        (1 + 4 / c) * ε ≤ (1 - c / 4) * δ + c * η / 8 := by
  have hfilter := normalized_filter_error_le hc hc1 hδ0 hδ
  have heps : (1 + 4 / c) * ε ≤ c * η / 8 := by
    have hcoef : 0 ≤ 1 + 4 / c := by positivity
    calc
      _ ≤ (1 + 4 / c) * (c ^ 2 * η / 40) := mul_le_mul_of_nonneg_left hε hcoef
      _ = c * η * (c + 4) / 40 := by field_simp
      _ ≤ c * η / 8 := by nlinarith [mul_nonneg hc.le hη]
  have hscale := mul_le_mul_of_nonneg_left hfilter (by positivity : 0 ≤ 1 + c / 4)
  have hdecrease : (1 + c / 4) * ((1 - c / 2) * δ) ≤ (1 - c / 4) * δ := by
    nlinarith [mul_nonneg (sq_nonneg c) hδ0]
  linarith

/-- A nearby Schmidt-rank reference and the actual collective trimming increment
fit the stable recurrence. The free robustness weight is `c/16`. This is an
auxiliary estimate for the reference-space argument in ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1813. -/
theorem reference_filter_trim_error_le {c δ ε ζ η : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hζ0 : 0 ≤ ζ)
    (hε : ε ≤ c ^ 2 * η / 1024) (hζ : ζ ≤ c * η / 48) :
    (1 + c / 16) * ((1 + c / 16) *
        ((1 - c) * δ / (1 - δ + (1 - c) * δ)) + (1 + 16 / c) * ε + 2 * ζ) +
      (1 + 16 / c) * ε ≤ (1 - c / 4) * δ + c * η / 8 := by
  have hf := normalized_filter_error_le hc hc1 hδ0 hδ
  have hscale := mul_le_mul_of_nonneg_left hf (sq_nonneg (1 + c / 16))
  have hcoeff : (1 + c / 16) ^ 2 * (1 - c / 2) ≤ 1 - c / 4 := by
    nlinarith [mul_nonneg (sq_nonneg c) hc.le]
  have hfilt : (1 + c / 16) ^ 2 *
      ((1 - c) * δ / (1 - δ + (1 - c) * δ)) ≤ (1 - c / 4) * δ := by
    calc
      _ ≤ (1 + c / 16) ^ 2 * ((1 - c / 2) * δ) := hscale
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoeff hδ0]
  have hepsCoeff : (2 + c / 16) * (1 + 16 / c) ≤ 64 / c := by
    apply (mul_le_mul_iff_right₀ hc).mp
    field_simp
    nlinarith [sq_nonneg (1 - c)]
  have heps : (2 + c / 16) * (1 + 16 / c) * ε ≤ c * η / 16 := by
    calc
      _ ≤ (64 / c) * ε := mul_le_mul_of_nonneg_right hepsCoeff hε0
      _ ≤ (64 / c) * (c ^ 2 * η / 1024) := by gcongr
      _ = _ := by field_simp; ring
  have hz : 2 * (1 + c / 16) * ζ ≤ c * η / 16 := by
    calc
      _ ≤ 3 * ζ := by nlinarith
      _ ≤ 3 * (c * η / 48) := by gcongr
      _ = _ := by ring
  nlinarith

/-- Stability and a geometric upper bound for a filter-and-trim recurrence.
This is an auxiliary numerical estimate for ALVV, arXiv:1602.08828v2,
Algorithm `t:alg1`, lines 1634–1640. -/
theorem filter_trim_iterate_le {c η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (u : ℕ → ℝ) (hu : u 0 ≤ 1 / 2)
    (hstep : ∀ n, u n ≤ 1 / 2 → u (n + 1) ≤ (1 - c / 4) * u n + c * η / 8) :
    (∀ n, u n ≤ 1 / 2) ∧ ∀ n, u n ≤ (1 - c / 4) ^ n * u 0 + η / 2 := by
  have hq : 0 ≤ 1 - c / 4 := by linarith
  have hinv : ∀ n, u n ≤ 1 / 2 := by
    intro n
    induction n with
    | zero => exact hu
    | succ n ih =>
      have hs := hstep n ih
      have hh := mul_le_mul_of_nonneg_left ih hq
      nlinarith [mul_le_mul_of_nonneg_left hη hc.le]
  refine ⟨hinv, ?_⟩
  intro n
  induction n with
  | zero => simp only [pow_zero, one_mul]; linarith
  | succ n ih =>
    have hs := hstep n (hinv n)
    have hh := mul_le_mul_of_nonneg_left ih hq
    rw [pow_succ]
    nlinarith

/-- Every positive target error is reached after finitely many stable filter-and-trim
steps. This auxiliary estimate concerns the recurrence in ALVV,
arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640; it does not supply the
physical trimming subspaces or the final compressed spectral subspace. -/
theorem exists_filter_trim_iteration {c η : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hη0 : 0 < η) (hη : η ≤ 1) (u : ℕ → ℝ) (hu : u 0 ≤ 1 / 2)
    (hstep : ∀ n, u n ≤ 1 / 2 → u (n + 1) ≤ (1 - c / 4) * u n + c * η / 8) :
    ∃ n, u n ≤ η := by
  have hb := (filter_trim_iterate_le hc hc1 hη0.le hη u hu hstep).2
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < η / 2)
    (by linarith : 1 - c / 4 < 1)
  refine ⟨n, ?_⟩
  have hh : (1 - c / 4) ^ n * u 0 ≤ (1 - c / 4) ^ n := by
    exact mul_le_of_le_one_right (pow_nonneg (by linarith) _) (by linarith)
  linarith [hb n]

end Real
