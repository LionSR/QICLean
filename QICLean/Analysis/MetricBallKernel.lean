/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ExponentialDistanceProfile

/-!
# Incidence kernels of finite-radius metric balls

A finite family of labelled anchors defines a kernel counting the balls that
contain a pair of sites. The row bound counts anchor labels and sites
separately, so repeated anchor positions retain their multiplicity.

These independently authored supporting lemmas isolate the single-radius
counting argument in `09-amplification.tex`, lines 141–159, at source revision
`adc7f124`. They do not assert the channel or Poisson evolution statements.
-/

open scoped BigOperators ENNReal NNReal

namespace Metric

variable {ι κ : Type*} [Fintype ι] [PseudoEMetricSpace κ]

/-- The number of labelled radius-`r` balls containing both sites, regarded as
a real kernel. Anchor labels remain distinct even when their positions agree. -/
noncomputable def ballIncidenceKernel (anchor : ι → κ) (r : ℝ≥0) (y z : κ) : ℝ := by
  classical
  exact ∑ i : ι, if edist y (anchor i) ≤ r ∧ edist z (anchor i) ≤ r then 1 else 0

lemma ballIncidenceKernel_nonneg (anchor : ι → κ) (r : ℝ≥0) (y z : κ) :
    0 ≤ ballIncidenceKernel anchor r y z := by
  classical
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

/-- Two sites in one finite-radius ball have finite extended distance, and
real distance at most twice the radius. Finiteness is established using the
extended triangle inequality before passing to real distances. -/
lemma edist_ne_top_and_toReal_le_two_mul_of_ball_bounds {x y z : κ} {r : ℝ≥0}
    (hy : edist y x ≤ r) (hz : edist z x ≤ r) :
    edist y z ≠ ∞ ∧ (edist y z).toReal ≤ 2 * (r : ℝ) := by
  have hdist : edist y z ≤ (r : ℝ≥0∞) + r :=
    (edist_triangle_right y z x).trans (add_le_add hy hz)
  have hfinite : edist y z ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩) hdist
  refine ⟨hfinite, ?_⟩
  simpa [two_mul] using
    ENNReal.toReal_le_add hdist ENNReal.coe_ne_top ENNReal.coe_ne_top

/-- The literal incidence kernel has no entries between components at
infinite extended distance. -/
lemma ballIncidenceKernel_eq_zero_of_edist_eq_top (anchor : ι → κ) (r : ℝ≥0)
    {y z : κ} (hyz : edist y z = ∞) : ballIncidenceKernel anchor r y z = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  have hnot : ¬(edist y (anchor i) ≤ r ∧ edist z (anchor i) ≤ r) := by
    intro h
    exact (edist_ne_top_and_toReal_le_two_mul_of_ball_bounds h.1 h.2).1 hyz
  simp [hnot]

open Classical in
/-- A single kernel entry is bounded by the actual number of anchor labels
whose balls contain its first site. -/
lemma ballIncidenceKernel_le_card_labels (anchor : ι → κ) (r : ℝ≥0) (y z : κ) :
    ballIncidenceKernel anchor r y z ≤
      ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ r).card : ℝ) := by
  calc
    _ ≤ ∑ i : ι, if edist y (anchor i) ≤ r then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp_all
    _ = _ := by rw [← Finset.sum_filter]; simp

open Classical in
/-- The single-radius weighted row estimate behind
`09-amplification.tex`, lines 141–159. Both hypotheses count actual finite
sets: labels whose balls contain `y`, and sites in each anchor's ball.
The exponent retains the exact factor `2 * r`; zero radii and empty label
or site types require no exceptions. -/
theorem sum_ballIncidenceKernel_mul_exp_le [Fintype κ]
    (anchor : ι → κ) (r : ℝ≥0) {a α B V : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (y : κ)
    (hlabels : ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ r).card : ℝ) ≤ B)
    (hballs : ∀ i : ι,
      ((Finset.univ.filter fun z : κ ↦ edist z (anchor i) ≤ r).card : ℝ) ≤ V) :
    (∑ z : κ, ballIncidenceKernel anchor r y z *
      Real.exp (a * (edist y z).toReal ^ α)) ≤
      B * V * Real.exp (a * (2 * (r : ℝ)) ^ α) := by
  let E := Real.exp (a * (2 * (r : ℝ)) ^ α)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hexp (i : ι) (z : κ) (hy : edist y (anchor i) ≤ r)
      (hz : edist z (anchor i) ≤ r) : Real.exp (a * (edist y z).toReal ^ α) ≤ E := by
    obtain ⟨_, hdist⟩ := edist_ne_top_and_toReal_le_two_mul_of_ball_bounds hy hz
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ENNReal.toReal_nonneg hdist hα) ha)
  calc
    _ = ∑ i : ι, ∑ z : κ, if edist y (anchor i) ≤ r ∧ edist z (anchor i) ≤ r
        then Real.exp (a * (edist y z).toReal ^ α) else 0 := by
      simp only [ballIncidenceKernel, Finset.sum_mul, ite_mul, one_mul, zero_mul]
      exact Finset.sum_comm
    _ ≤ ∑ i : ι, if edist y (anchor i) ≤ r then
        ((Finset.univ.filter fun z : κ ↦ edist z (anchor i) ≤ r).card : ℝ) * E else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hy : edist y (anchor i) ≤ r
      · simp only [hy, true_and, ite_true]
        rw [← Finset.sum_filter]
        calc
          _ ≤ ∑ z ∈ Finset.univ.filter (fun z : κ ↦ edist z (anchor i) ≤ r), E := by
            apply Finset.sum_le_sum
            intro z hz
            exact hexp i z hy (Finset.mem_filter.mp hz).2
          _ = _ := by simp
      · simp [hy]
    _ ≤ ∑ i : ι, if edist y (anchor i) ≤ r then V * E else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact mul_le_mul_of_nonneg_right (hballs i) hE
      · exact le_rfl
    _ = ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ r).card : ℝ) * (V * E) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ B * (V * E) := mul_le_mul hlabels le_rfl (mul_nonneg hV hE) hB
    _ = _ := (mul_assoc B V E).symm

end Metric
