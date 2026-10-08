/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MetricBallKernel
import QICLean.Analysis.StretchedExponentialSummability

/-!
# Stretched-exponential sums of ball incidence kernels

The literal shell series is summable under a quadratic bound on the number of
anchor labels near each site. A quadratic bound on the sites in every anchor
ball then gives a uniform weighted row estimate, with a fourth polynomial
moment and the exact remaining decay rate `c - a * 2 ^ α`.

These independently authored estimates establish the geometric shell bound in
`09-amplification.tex`, lines 141–159, at source revision `adc7f124`. They do not
identify a physical oscillation channel or construct a Poisson clock process.
-/

open scoped BigOperators ENNReal NNReal

namespace Metric

variable {ι κ : Type*} [Fintype ι] [PseudoEMetricSpace κ]

/-- The literal sum of the radius-`n` incidence kernels with stretched-exponential
shell amplitudes. Repeated anchors are counted by their distinct labels. -/
noncomputable def stretchedBallKernel (anchor : ι → κ) (C c α : ℝ) (y z : κ) : ℝ :=
  ∑' n : ℕ, C * Real.exp (-c * (n : ℝ) ^ α) *
    ballIncidenceKernel anchor (n : ℝ≥0) y z

lemma stretchedBallKernel_nonneg (anchor : ι → κ) {C c α : ℝ} (hC : 0 ≤ C)
    (y z : κ) : 0 ≤ stretchedBallKernel anchor C c α y z := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le)
    (ballIncidenceKernel_nonneg anchor _ y z)

/-- No shell connects sites whose extended distance is infinite. -/
lemma stretchedBallKernel_eq_zero_of_edist_eq_top (anchor : ι → κ) (C c α : ℝ)
    {y z : κ} (hyz : edist y z = ∞) : stretchedBallKernel anchor C c α y z = 0 := by
  simp [stretchedBallKernel, ballIncidenceKernel_eq_zero_of_edist_eq_top anchor _ hyz]

open Classical in
/-- Actual quadratic label counts give genuine convergence of every entry's
shell series, before any exchange of a finite site sum with an infinite sum. -/
theorem summable_stretchedBallKernel (anchor : ι → κ) {C c α B : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (y z : κ)
    (hlabels : ∀ n : ℕ,
      ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        B * (1 + (n : ℝ)) ^ 2) :
    Summable (fun n : ℕ ↦ C * Real.exp (-c * (n : ℝ) ^ α) *
      ballIncidenceKernel anchor (n : ℝ≥0) y z) := by
  apply ((Real.summable_nat_pow_mul_exp_neg_mul_rpow 2 hc hα).mul_left (C * B)).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le)
    (ballIncidenceKernel_nonneg anchor _ y z))]
  calc
    _ ≤ C * Real.exp (-c * (n : ℝ) ^ α) * (B * (1 + (n : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        ((ballIncidenceKernel_le_card_labels anchor _ y z).trans (hlabels n))
        (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring

open Classical in
/-- The full weighted row of the literal shell kernel is bounded independently
of the total numbers of sites and labels. Only the two actual quadratic
geometric counting bounds enter the constant. The remaining stretched-
exponential rate is exactly `c - a * 2 ^ α`. -/
theorem sum_stretchedBallKernel_mul_exp_le [Fintype κ]
    (anchor : ι → κ) {C c α a B V : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hα : 0 < α) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hdecay : 0 < c - a * 2 ^ α)
    (hlabels : ∀ (n : ℕ) (y : κ),
      ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        B * (1 + (n : ℝ)) ^ 2)
    (hballs : ∀ (n : ℕ) (i : ι),
      ((Finset.univ.filter fun z : κ ↦ edist z (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        V * (1 + (n : ℝ)) ^ 2)
    (y : κ) :
    (∑ z : κ, stretchedBallKernel anchor C c α y z *
      Real.exp (a * (edist y z).toReal ^ α)) ≤
      C * B * V * ∑' n : ℕ,
        (1 + (n : ℝ)) ^ 4 * Real.exp (-(c - a * 2 ^ α) * (n : ℝ) ^ α) := by
  have hc : 0 < c := by
    have hnonneg : 0 ≤ a * (2 : ℝ) ^ α := mul_nonneg ha (Real.rpow_nonneg (by norm_num) _)
    linarith
  have hentry (z : κ) := summable_stretchedBallKernel anchor hC hc hα y z
    (fun n ↦ hlabels n y)
  have hweighted (z : κ) := (hentry z).mul_right (Real.exp (a * (edist y z).toReal ^ α))
  have hrows := summable_sum (fun z (_ : z ∈ (Finset.univ : Finset κ)) ↦ hweighted z)
  have hmajorant := (Real.summable_nat_pow_mul_exp_neg_mul_rpow 4 hdecay hα).mul_left (C * B * V)
  have hshell (n : ℕ) :
      (∑ z : κ, (C * Real.exp (-c * (n : ℝ) ^ α) *
        ballIncidenceKernel anchor (n : ℝ≥0) y z) *
          Real.exp (a * (edist y z).toReal ^ α)) ≤
      C * B * V * ((1 + (n : ℝ)) ^ 4 *
        Real.exp (-(c - a * 2 ^ α) * (n : ℝ) ^ α)) := by
    have hone := sum_ballIncidenceKernel_mul_exp_le anchor (n : ℝ≥0)
      ha hα.le (mul_nonneg hB (sq_nonneg _)) (mul_nonneg hV (sq_nonneg _)) y
      (hlabels n y) (hballs n)
    have hexp : Real.exp (-c * (n : ℝ) ^ α) *
        Real.exp (a * (2 * (n : ℝ)) ^ α) =
        Real.exp (-(c - a * 2 ^ α) * (n : ℝ) ^ α) := by
      rw [← Real.exp_add, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
      congr 1
      ring
    calc
      _ = (C * Real.exp (-c * (n : ℝ) ^ α)) *
          ∑ z : κ, ballIncidenceKernel anchor (n : ℝ≥0) y z *
            Real.exp (a * (edist y z).toReal ^ α) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ ≤ (C * Real.exp (-c * (n : ℝ) ^ α)) *
          ((B * (1 + (n : ℝ)) ^ 2) * (V * (1 + (n : ℝ)) ^ 2) *
            Real.exp (a * (2 * (n : ℝ)) ^ α)) := by
        exact mul_le_mul_of_nonneg_left (by simpa using hone) (mul_nonneg hC (Real.exp_pos _).le)
      _ = C * B * V * (1 + (n : ℝ)) ^ 4 *
          (Real.exp (-c * (n : ℝ) ^ α) * Real.exp (a * (2 * (n : ℝ)) ^ α)) := by ring
      _ = _ := by rw [hexp]; ring
  calc
    _ = ∑' n : ℕ, ∑ z : κ, (C * Real.exp (-c * (n : ℝ) ^ α) *
          ballIncidenceKernel anchor (n : ℝ≥0) y z) *
            Real.exp (a * (edist y z).toReal ^ α) := by
      simp_rw [stretchedBallKernel, ← tsum_mul_right]
      exact (Summable.tsum_finsetSum (fun z _ ↦ hweighted z)).symm
    _ ≤ ∑' n : ℕ, C * B * V * ((1 + (n : ℝ)) ^ 4 *
        Real.exp (-(c - a * 2 ^ α) * (n : ℝ) ^ α)) :=
      hrows.tsum_le_tsum hshell hmajorant
    _ = _ := tsum_mul_left

open Classical in
/-- The explicit positive weight `c / (2 * 2 ^ α)` leaves exactly half of the
original decay rate, making the uniform fourth-moment constant concrete. -/
theorem sum_stretchedBallKernel_mul_exp_half_rate_le [Fintype κ]
    (anchor : ι → κ) {C c α B V : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hlabels : ∀ (n : ℕ) (y : κ),
      ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        B * (1 + (n : ℝ)) ^ 2)
    (hballs : ∀ (n : ℕ) (i : ι),
      ((Finset.univ.filter fun z : κ ↦ edist z (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        V * (1 + (n : ℝ)) ^ 2) :
    0 < c / (2 * 2 ^ α) ∧ ∀ y : κ,
      (∑ z : κ, stretchedBallKernel anchor C c α y z *
        Real.exp ((c / (2 * 2 ^ α)) * (edist y z).toReal ^ α)) ≤
        C * B * V * ∑' n : ℕ,
          (1 + (n : ℝ)) ^ 4 * Real.exp (-(c / 2) * (n : ℝ) ^ α) := by
  have htwo : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have ha : 0 < c / (2 * 2 ^ α) := div_pos hc (mul_pos (by norm_num) htwo)
  have hrate : c - c / (2 * 2 ^ α) * 2 ^ α = c / 2 := by
    field_simp
    ring
  refine ⟨ha, fun y ↦ ?_⟩
  simpa only [hrate] using sum_stretchedBallKernel_mul_exp_le anchor hC ha.le hα hB hV
    (show 0 < c - c / (2 * 2 ^ α) * 2 ^ α by rw [hrate]; exact half_pos hc)
    hlabels hballs y

end Metric
