/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ConeNormBound
import Mathlib.Algebra.Order.Ring.Prod
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# A boundary fixed point does not bound the spectrum

Wolf, *Quantum Channels & Operations*, Eq. (8.91), local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1028–1037.
The bracketed source note proposes allowing a boundary fixed point and infinite
projective diameter. The positive map `(x,y) ↦ (x,2y)` fixes `(1,0)` but has eigenvalue
`2` on `(0,1)`. Thus an unrestricted extension with the convention \(\tanh(\infty) = 1\) fails.
Without an infinite-diameter convention, the displayed expression is undefined
on this example. The finite-diameter/interior-fixed-point theorem is not refuted,
and no corrected spectral-diameter theorem is supplied.
-/

noncomputable section

namespace ProjectiveDiameterCounterexample

/-- The closed positive quadrant. -/
def quadrant : ProperCone ℝ (ℝ × ℝ) := ProperCone.positive ℝ (ℝ × ℝ)

/-- A positive diagonal map with a fixed boundary ray and an expanding ray. -/
def diagonalMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.1, 2 * x.2)
  map_add' x y := by ext <;> simp; ring
  map_smul' r x := by ext <;> simp; ring

/-- Membership in the closed positive quadrant is coordinatewise nonnegativity. -/
lemma mem_quadrant (x : ℝ × ℝ) : x ∈ quadrant ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 := Iff.rfl

lemma diagonalMap_positive (x : ℝ × ℝ) (hx : x ∈ quadrant) :
    diagonalMap x ∈ quadrant := by
  exact ⟨hx.1, mul_nonneg (by norm_num) hx.2⟩

/-- The fixed-point and eigenvector conditions of the proposed unrestricted extension,
with an eigenvalue exceeding every coefficient bounded by one. -/
theorem boundary_fixed_point_counterexample :
    (∀ x ∈ quadrant, diagonalMap x ∈ quadrant) ∧
    ((1, 0) : ℝ × ℝ) ∈ quadrant ∧ ((1, 0) : ℝ × ℝ) ≠ 0 ∧
    diagonalMap (1, 0) = (1, 0) ∧
    ((0, 1) : ℝ × ℝ) ≠ 0 ∧ diagonalMap (0, 1) = (2 : ℝ) • (0, 1) ∧
    (¬ ∃ r : ℝ, ((0, 1) : ℝ × ℝ) = r • (1, 0)) ∧
    (∀ k : ℝ, k ≤ 1 → ¬ |(2 : ℝ)| ≤ k) := by
  refine ⟨diagonalMap_positive, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num⟩
  · simp
  · ext <;> norm_num [diagonalMap]
  · simp
  · ext <;> norm_num [diagonalMap]
  · rintro ⟨r, hr⟩
    have := congrArg Prod.snd hr
    simp at this
  · intro k hk
    norm_num
    linarith

/-- Failure for every real diameter parameter as well. The infinite-diameter
case is covered by the stronger coefficient bound in the preceding theorem. -/
theorem eigenvalue_gt_tanh (D : ℝ) : Real.tanh (D / 4) < |(2 : ℝ)| := by
  have := Real.tanh_lt_one (D / 4)
  norm_num
  linarith

/-- The lower ratio of `(1,t)` to `(1,1)` when `t ≥ 1`. -/
lemma lowerRatio_first {t : ℝ} (ht : 1 ≤ t) :
    quadrant.lowerRatio (1, t) (1, 1) = 1 := by
  unfold ProperCone.lowerRatio
  apply le_antisymm
  · apply csSup_le ⟨0, by simp [mem_quadrant]; linarith⟩
    intro r hr
    have h := hr.2.1
    change 0 ≤ 1 - r * 1 at h
    linarith
  · apply le_csSup
    · refine ⟨1, ?_⟩
      intro r hr
      have h := hr.2.1
      change 0 ≤ 1 - r * 1 at h
      linarith
    · constructor
      · norm_num
      · change 0 ≤ 1 - 1 * 1 ∧ 0 ≤ t - 1 * 1
        constructor <;> linarith

/-- The reverse ratio, including the reciprocal scale. -/
lemma lowerRatio_second {t : ℝ} (ht : 1 ≤ t) :
    quadrant.lowerRatio (1, 1) (1, t) = 1 / t := by
  have htpos : 0 < t := by linarith
  unfold ProperCone.lowerRatio
  have hb : ∀ r ∈ {r : ℝ | 0 ≤ r ∧ (1, 1) - r • (1, t) ∈ quadrant}, r ≤ 1 / t := by
    intro r hr
    have h := hr.2.2
    change 0 ≤ 1 - r * t at h
    exact (le_div_iff₀ htpos).mpr (by linarith)
  apply le_antisymm
  · exact csSup_le ⟨0, by simp [mem_quadrant]⟩ hb
  · apply le_csSup ⟨1 / t, hb⟩
    refine ⟨by positivity, ?_⟩
    change 0 ≤ 1 - 1 / t * 1 ∧ 0 ≤ 1 - 1 / t * t
    constructor
    · have : 1 / t ≤ 1 := (div_le_one htpos).mpr ht
      linarith
    · rw [div_mul_cancel₀ _ htpos.ne']
      norm_num

/-- The output logarithmic distances are unbounded on strictly positive inputs.
The strict coordinate inequalities describe the interior of the quadrant. -/
theorem output_log_distance_unbounded (R : ℝ) :
    ∃ a b : ℝ × ℝ, (0 < a.1 ∧ 0 < a.2) ∧ (0 < b.1 ∧ 0 < b.2) ∧
      R < -Real.log (quadrant.lowerRatio (diagonalMap a) (diagonalMap b) *
        quadrant.lowerRatio (diagonalMap b) (diagonalMap a)) := by
  let t := Real.exp (max R 0 + 1)
  have ht : 1 ≤ t := Real.one_le_exp_iff.mpr (by positivity)
  have htpos : 0 < t := Real.exp_pos _
  refine ⟨(1, t / 2), (1, 1 / 2), ⟨by norm_num, by positivity⟩,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  have ha : diagonalMap (1, t / 2) = (1, t) := by ext <;> simp [diagonalMap]; ring
  have hb : diagonalMap (1, 1 / 2) = (1, 1) := by ext <;> norm_num [diagonalMap]
  rw [ha, hb, lowerRatio_first ht, lowerRatio_second ht, one_mul,
    one_div, Real.log_inv, neg_neg, Real.log_exp]
  have := le_max_left R 0
  linarith

end ProjectiveDiameterCounterexample
