/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Nets of subsets of the unit ball by a volume argument

In a real normed space of dimension `n`, a set of points of the closed unit ball at pairwise
distance at least `ε` has at most `(1 + 2/ε) ^ n` elements: the open balls of radius `ε/2` about
the points are disjoint and lie in the ball of radius `1 + ε/2`, and Haar measure scales balls of
radius `r` by `r ^ n`. A maximal `ε`-separated subset of a set `A` in the unit ball is therefore
finite, and it is an `ε`-net of `A`.

This is the volume argument cited by Arad, Landau, Vazirani and Vidick (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, proof of Lemma `l:rs`, lines 541–546) from Vershynin, *Introduction to
the non-asymptotic analysis of random matrices*, Lemma 5.2. The points of the net are taken in `A`
itself, so a net of the unit sphere consists of unit vectors.

## Main statements

* `Metric.card_le_of_le_dist_of_subset_closedBall`: the volume bound on separated sets.
* `Metric.exists_finset_net_of_subset_closedBall`: an `ε`-net of `A ⊆ closedBall 0 1` inside `A`
  with at most `(1 + 2/ε) ^ n` points.
-/

open MeasureTheory Module

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Volume bound.** A finite subset of the closed unit ball whose distinct points are at
distance at least `ε > 0` has at most `(1 + 2/ε) ^ n` elements, `n = finrank ℝ E`. -/
theorem card_le_of_le_dist_of_subset_closedBall {ε : ℝ} (hε : 0 < ε) {C : Finset E}
    (hC : (C : Set E) ⊆ closedBall 0 1) (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) :
    (C.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E := by
  borelize E
  set μ : Measure E := Measure.addHaar
  set n := finrank ℝ E
  have hε2 : 0 < ε / 2 := half_pos hε
  have hB0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hBtop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hdisj : (C : Set E).PairwiseDisjoint fun c => ball c (ε / 2) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hsub : (⋃ c ∈ C, ball c (ε / 2)) ⊆ ball 0 (1 + ε / 2) := by
    simp only [Set.iUnion_subset_iff]
    intro c hc z hz
    have h1 : ‖c‖ ≤ 1 := by simpa using hC hc
    rw [mem_ball, dist_zero_right]
    calc ‖z‖ ≤ ‖c‖ + dist z c := by
          simpa [dist_eq_norm] using norm_le_norm_add_norm_sub' z c
      _ < 1 + ε / 2 := by rw [mem_ball] at hz; linarith
  have hvol : (C.card : ENNReal) * (ENNReal.ofReal ((ε / 2) ^ n) * μ (ball 0 1)) ≤
      ENNReal.ofReal ((1 + ε / 2) ^ n) * μ (ball 0 1) := by
    calc (C.card : ENNReal) * (ENNReal.ofReal ((ε / 2) ^ n) * μ (ball 0 1))
        = ∑ c ∈ C, μ (ball c (ε / 2)) := by
          rw [Finset.sum_congr rfl fun c _ => Measure.addHaar_ball_of_pos μ c hε2,
            Finset.sum_const, nsmul_eq_mul]
      _ = μ (⋃ c ∈ C, ball c (ε / 2)) :=
          (measure_biUnion_finset hdisj fun c _ => measurableSet_ball).symm
      _ ≤ μ (ball 0 (1 + ε / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((1 + ε / 2) ^ n) * μ (ball 0 1) :=
          Measure.addHaar_ball_of_pos μ 0 (by linarith)
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBtop, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
  have hpos : 0 < (ε / 2) ^ n := pow_pos hε2 n
  calc (C.card : ℝ) ≤ (1 + ε / 2) ^ n / (ε / 2) ^ n := (le_div_iff₀ hpos).mpr hvol
    _ = (1 + 2 / ε) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
      ring

/-- **Volume net.** Every subset `A` of the closed unit ball has an `ε`-net `C ⊆ A` with at most
`(1 + 2/ε) ^ n` points, `n = finrank ℝ E`: every point of `A` lies within `ε` of a point of `C`.
Vershynin, Lemma 5.2, as used in the proof of Lemma `l:rs` of arXiv:1602.08828v2
(lines 541–546). -/
theorem exists_finset_net_of_subset_closedBall {ε : ℝ} (hε : 0 < ε) {A : Set E}
    (hA : A ⊆ closedBall 0 1) :
    ∃ C : Finset E, (C : Set E) ⊆ A ∧ (C.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E ∧
      ∀ x ∈ A, ∃ c ∈ C, dist x c ≤ ε := by
  classical
  set N := ⌊(1 + 2 / ε) ^ finrank ℝ E⌋₊
  let P : ℕ → Prop := fun m => ∃ C : Finset E, (C : Set E) ⊆ A ∧
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) ∧ C.card = m
  have hcard : ∀ C : Finset E, (C : Set E) ⊆ A → (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) →
      C.card ≤ N := fun C hCA hsep =>
    Nat.le_floor (card_le_of_le_dist_of_subset_closedBall hε (hCA.trans hA)
      fun x hx y hy hxy => (hsep x hx y hy hxy).le)
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  obtain ⟨C, hCA, hsep, hCm⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  refine ⟨C, hCA, ?_, fun x hx => ?_⟩
  · calc (C.card : ℝ) ≤ N := by exact_mod_cast hcard C hCA hsep
      _ ≤ (1 + 2 / ε) ^ finrank ℝ E := Nat.floor_le (by positivity)
  · by_contra! hfar
    have hxC : x ∉ C := fun hxC => by
      have := hfar x hxC
      rw [dist_self] at this
      linarith
    have hsep' : ∀ y ∈ insert x C, ∀ z ∈ insert x C, y ≠ z → ε < dist y z := by
      intro y hy z hz hyz
      rw [Finset.mem_insert] at hy hz
      rcases hy with rfl | hy <;> rcases hz with rfl | hz
      · exact absurd rfl hyz
      · exact hfar z hz
      · rw [dist_comm]
        exact hfar y hy
      · exact hsep y hy z hz hyz
    have hins : P (C.card + 1) :=
      ⟨insert x C, by simp [Set.insert_subset_iff, hx, hCA], hsep',
        Finset.card_insert_of_notMem hxC⟩
    have hle : C.card + 1 ≤ N := by
      rw [← Finset.card_insert_of_notMem hxC]
      exact hcard _ (by simp [Set.insert_subset_iff, hx, hCA]) hsep'
    have := Nat.le_findGreatest hle hins
    omega

end Metric
