/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field

/-!
# Harmonic weights of total mass two

For positive costs `c_j`, `j ∈ s`, put `Z = ∑ 1/c_j` and `a_j = 2/(Z c_j)`. These weights
have total mass two and quadratic cost `∑ c_j a_j² = 4/Z`, which is the least quadratic
cost among all weights of total mass two (Cauchy–Schwarz). For the nested contours
`c_j = 2r + jD`, `1 ≤ j ≤ m`, with `D(m+1) > (P-1) r` and `r ≥ 1`, the sum satisfies
`Z ≥ (1/D) log ((P+1)/(2+D))`, uniformly in `r`.

## Main results

* `Entropy.sum_harmonicWeight`, `Entropy.sum_mul_harmonicWeight_sq`: mass and cost.
* `Entropy.harmonic_cost_le`: optimality among weights of total mass two.
* `Entropy.log_div_le_sum_inv_contour`: the integral comparison for nested contours.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 3.2
  (`lem:initial-buffer`), `02-initial.tex`, lines 300–333, `eq:initial-harmonic-weights`
  and `eq:initial-harmonic-lower`.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators

namespace Entropy

variable {ι : Type*}

/-- The harmonic weight `a_j = 2/(Z c_j)` with `Z = ∑ 1/c_j`.
Area-law manuscript, `02-initial.tex`, line 320, `eq:initial-harmonic-weights`. -/
noncomputable def harmonicWeight (s : Finset ι) (c : ι → ℝ) (j : ι) : ℝ :=
  2 / ((∑ i ∈ s, 1 / c i) * c j)

theorem sum_inv_pos {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty) (hc : ∀ j ∈ s, 0 < c j) :
    0 < ∑ i ∈ s, 1 / c i :=
  Finset.sum_pos (fun i hi ↦ one_div_pos.mpr (hc i hi)) hs

/-- The harmonic weights have total mass two. -/
theorem sum_harmonicWeight {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty)
    (hc : ∀ j ∈ s, 0 < c j) : ∑ j ∈ s, harmonicWeight s c j = 2 := by
  have hZ := sum_inv_pos hs hc
  simp only [harmonicWeight]
  have : ∀ j ∈ s, 2 / ((∑ i ∈ s, 1 / c i) * c j) = 2 / (∑ i ∈ s, 1 / c i) * (1 / c j) :=
    fun j hj ↦ by field_simp
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, div_mul_cancel₀ _ hZ.ne']

/-- The quadratic cost of the harmonic weights is `4/Z`. -/
theorem sum_mul_harmonicWeight_sq {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty)
    (hc : ∀ j ∈ s, 0 < c j) :
    ∑ j ∈ s, c j * harmonicWeight s c j ^ 2 = 4 / ∑ i ∈ s, 1 / c i := by
  have hZ := sum_inv_pos hs hc
  simp only [harmonicWeight]
  have : ∀ j ∈ s, c j * (2 / ((∑ i ∈ s, 1 / c i) * c j)) ^ 2 =
      4 / (∑ i ∈ s, 1 / c i) ^ 2 * (1 / c j) := fun j hj ↦ by
    have := (hc j hj).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  field_simp

/-- **Optimality of the harmonic weights.** Every family of weights of total mass two has
quadratic cost at least `4/Z`.
Area-law manuscript, `02-initial.tex`, lines 310–317. -/
theorem harmonic_cost_le {s : Finset ι} {c : ι → ℝ} (hs : s.Nonempty)
    (hc : ∀ j ∈ s, 0 < c j) {b : ι → ℝ} (hb : ∑ j ∈ s, b j = 2) :
    4 / ∑ i ∈ s, 1 / c i ≤ ∑ j ∈ s, c j * b j ^ 2 := by
  have hZ := sum_inv_pos hs hc
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j ↦ Real.sqrt (c j) * b j)
    (fun j ↦ 1 / Real.sqrt (c j))
  have h1 : ∑ j ∈ s, Real.sqrt (c j) * b j * (1 / Real.sqrt (c j)) = 2 := by
    rw [← hb]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Real.sqrt_pos.mpr (hc j hj)
    field_simp
  have h2 : ∑ j ∈ s, (Real.sqrt (c j) * b j) ^ 2 = ∑ j ∈ s, c j * b j ^ 2 :=
    Finset.sum_congr rfl fun j hj ↦ by rw [mul_pow, Real.sq_sqrt (hc j hj).le]
  have h3 : ∑ j ∈ s, (1 / Real.sqrt (c j)) ^ 2 = ∑ j ∈ s, 1 / c j :=
    Finset.sum_congr rfl fun j hj ↦ by rw [div_pow, one_pow, Real.sq_sqrt (hc j hj).le]
  rw [h1, h2, h3] at hcs
  rw [div_le_iff₀ hZ]
  linarith

/-- One step of the integral comparison: `log (x + D) - log x ≤ D / x`. -/
theorem log_add_sub_log_le_div {x D : ℝ} (hx : 0 < x) (hD : 0 ≤ D) :
    Real.log (x + D) - Real.log x ≤ D / x := by
  rw [← Real.log_div (by positivity) hx.ne']
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + D) / x by positivity)
  have : (x + D) / x - 1 = D / x := by field_simp; ring
  linarith

/-- **Integral comparison for nested contours.** For `r > 0`, `D > 0` and `m ≥ 0`,
`(1/D) log ((2r + D(m+1)) / (2r + D)) ≤ ∑_{j=1}^m 1/(2r + jD)`.
Area-law manuscript, `02-initial.tex`, lines 323–328, `eq:initial-harmonic-lower`. -/
theorem log_div_le_sum_inv_contour {r D : ℝ} (hr : 0 < r) (hD : 0 < D) (m : ℕ) :
    Real.log ((2 * r + D * (m + 1)) / (2 * r + D)) / D ≤
      ∑ j ∈ Finset.Icc 1 m, 1 / (2 * r + j * D) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpos : 0 < 2 * r + ((m + 1 : ℕ) : ℝ) * D := by positivity
    have hstep := log_add_sub_log_le_div hpos hD.le
    have hsplit : Real.log ((2 * r + D * (((m + 1 : ℕ) : ℝ) + 1)) / (2 * r + D)) =
        Real.log ((2 * r + D * ((m : ℝ) + 1)) / (2 * r + D)) +
          (Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D + D) -
            Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D)) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity)
        (by positivity)]
      push_cast
      ring_nf
    rw [hsplit, add_div]
    have h2 : (Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D + D) -
        Real.log (2 * r + ((m + 1 : ℕ) : ℝ) * D)) / D ≤ 1 / (2 * r + ((m + 1 : ℕ) : ℝ) * D) := by
      rw [div_le_iff₀ hD]
      calc _ ≤ D / (2 * r + ((m + 1 : ℕ) : ℝ) * D) := hstep
        _ = _ := by field_simp
    linarith

/-- **Uniform lower bound for the harmonic sum.** If `r ≥ 1`, `D > 0` and
`D (m + 1) ≥ (P - 1) r`, then `(1/D) log ((P + 1)/(2 + D)) ≤ ∑_{j=1}^m 1/(2r + jD)`.
Area-law manuscript, `02-initial.tex`, lines 323–331, `eq:initial-harmonic-lower`. -/
theorem log_div_le_sum_inv_contour_of_le {r D P : ℝ} (hr : 1 ≤ r) (hD : 0 < D)
    (hP : 1 ≤ P) {m : ℕ} (hm : (P - 1) * r ≤ D * (m + 1)) :
    Real.log ((P + 1) / (2 + D)) / D ≤ ∑ j ∈ Finset.Icc 1 m, 1 / (2 * r + j * D) := by
  refine le_trans ?_ (log_div_le_sum_inv_contour (by linarith) hD m)
  refine div_le_div_of_nonneg_right ?_ hD.le
  refine Real.log_le_log (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (P + 1) * r ≤ 2 * r + D * (m + 1) := by linarith
  have h2 : (P + 1) * (2 * r + D) ≤ (P + 1) * r * (2 + D) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ P + 1) hD.le)
      (by linarith : (0 : ℝ) ≤ r - 1)]
  have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 + D)
  linarith

end Entropy
