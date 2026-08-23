/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Topology.CompactRetractFixedPoint
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Fixed points on compact convex sets

This file proves the general compact-convex form of Brouwer's fixed-point
result, Wolf Theorem 6.10. The source states the theorem but does not
include a proof. We close the existing paper gap by the metric-projection route
recorded in `docs/paper-gaps/wolf_brouwer_general_compact_convex.tex`.

For a nonempty compact convex set `K` in a real inner-product space, a point
minimizing squared distance exists by compactness. Its variational inequality
implies that the resulting choice is unique implicitly (any two choices obey
the same estimate), is `1`-Lipschitz, and restricts to the identity on `K`.
It is therefore a continuous retraction, so
`fixedPoint_of_compact_retract` applies.

## Main definitions and results

* `CompactConvex.metricProjection`: a nearest point of a nonempty compact set.
* `CompactConvex.metricProjection_lipschitzWith`: convex metric projection is
  `1`-Lipschitz.
* `fixedPoint_of_compact_convex`: the coordinate-free compact-convex theorem.
* `brouwer_fixedPoint_compactConvex`: Wolf Theorem 6.10 for
  `S ⊆ Fin n → ℝ`.
-/

open scoped RealInnerProductSpace Topology

namespace CompactConvex

private theorem exists_metricProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (x : E) :
    ∃ p ∈ K, IsMinOn (fun z : E => ‖x - z‖ ^ 2) K p := by
  exact hK_comp.exists_isMinOn hK_ne (by fun_prop)

/-- A nearest point in a nonempty compact set, chosen by minimizing squared distance. -/
noncomputable def metricProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (x : E) : E :=
  Classical.choose (exists_metricProjection K hK_comp hK_ne x)

theorem metricProjection_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (x : E) :
    metricProjection K hK_comp hK_ne x ∈ K :=
  (Classical.choose_spec (exists_metricProjection K hK_comp hK_ne x)).1

theorem metricProjection_isMinOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (x : E) :
    IsMinOn (fun z : E => ‖x - z‖ ^ 2) K (metricProjection K hK_comp hK_ne x) :=
  (Classical.choose_spec (exists_metricProjection K hK_comp hK_ne x)).2

/-- The variational inequality obeyed by a squared-distance minimizer on a convex set. -/
theorem nearest_inner_nonpos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hK_conv : Convex ℝ K) {x p y : E}
    (hp : p ∈ K) (hmin : IsMinOn (fun z : E => ‖x - z‖ ^ 2) K p) (hy : y ∈ K) :
    inner ℝ (x - p) (y - p) ≤ 0 := by
  have htangent : y - p ∈ posTangentConeAt K p :=
    sub_mem_posTangentConeAt_of_segment_subset (hK_conv.segment_subset hp hy)
  have hderiv := ((hasFDerivAt_id p).const_sub x).norm_sq
  have hnonneg :=
    hmin.localize.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt htangent
  have hxp : inner ℝ x (y - p) ≤ inner ℝ p (y - p) := by
    simpa [smul_apply, ContinuousLinearMap.comp_apply] using hnonneg
  rw [inner_sub_left]
  exact sub_nonpos.mpr hxp

/-- Metric projection onto a compact convex set is nonexpansive. -/
theorem metricProjection_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (hK_conv : Convex ℝ K)
    (x y : E) :
    ‖metricProjection K hK_comp hK_ne x - metricProjection K hK_comp hK_ne y‖ ≤
      ‖x - y‖ := by
  let p := metricProjection K hK_comp hK_ne x
  let q := metricProjection K hK_comp hK_ne y
  have hp : p ∈ K := metricProjection_mem K hK_comp hK_ne x
  have hq : q ∈ K := metricProjection_mem K hK_comp hK_ne y
  have hx := nearest_inner_nonpos hK_conv hp
    (metricProjection_isMinOn K hK_comp hK_ne x) hq
  have hy := nearest_inner_nonpos hK_conv hq
    (metricProjection_isMinOn K hK_comp hK_ne y) hp
  have hx' : 0 ≤ inner ℝ (x - p) (p - q) := by
    rw [show q - p = -(p - q) by abel, inner_neg_right] at hx
    linarith
  have hy' : inner ℝ (y - q) (p - q) ≤ 0 := hy
  have hinner : ‖p - q‖ * ‖p - q‖ ≤ inner ℝ (x - y) (p - q) := by
    rw [← real_inner_self_eq_norm_mul_norm]
    rw [show x - y = (x - p) + (p - q) - (y - q) by abel]
    nth_rewrite 2 [inner_sub_left]
    rw [inner_add_left]
    linarith
  have hmul : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ :=
    hinner.trans (real_inner_le_norm (x - y) (p - q))
  change ‖p - q‖ ≤ ‖x - y‖
  by_cases hpq : p = q
  · simp [hpq]
  · have hpq_pos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
    nlinarith

theorem metricProjection_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (hK_conv : Convex ℝ K) :
    LipschitzWith 1 (metricProjection K hK_comp hK_ne) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    metricProjection_norm_sub_le K hK_comp hK_ne hK_conv x y

theorem continuous_metricProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (hK_conv : Convex ℝ K) :
    Continuous (metricProjection K hK_comp hK_ne) :=
  (metricProjection_lipschitzWith K hK_comp hK_ne hK_conv).continuous

theorem metricProjection_eq_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hK_comp : IsCompact K) (hK_ne : K.Nonempty) (hK_conv : Convex ℝ K)
    {x : E} (hx : x ∈ K) :
    metricProjection K hK_comp hK_ne x = x := by
  let p := metricProjection K hK_comp hK_ne x
  have hp : p ∈ K := metricProjection_mem K hK_comp hK_ne x
  have hinner : inner ℝ (x - p) (x - p) ≤ 0 :=
    nearest_inner_nonpos hK_conv hp (metricProjection_isMinOn K hK_comp hK_ne x) hx
  have hzero : x - p = 0 := real_inner_self_nonpos.mp hinner
  exact (sub_eq_zero.mp hzero).symm

end CompactConvex

/-- Wolf Theorem 6.10 in a finite-dimensional real inner-product space. -/
theorem fixedPoint_of_compact_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK_ne : K.Nonempty) (hK_comp : IsCompact K) (hK_conv : Convex ℝ K)
    {f : E → E} (hf_cont : ContinuousOn f K) (hf_maps : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  exact fixedPoint_of_compact_retract hK_comp
    (CompactConvex.continuous_metricProjection K hK_comp hK_ne hK_conv)
    (fun x _ => CompactConvex.metricProjection_mem K hK_comp hK_ne x)
    (fun _ hx => CompactConvex.metricProjection_eq_self hK_comp hK_ne hK_conv hx)
    hf_cont hf_maps

/-- Wolf Theorem 6.10 in its printed form for a subset of `ℝⁿ`. -/
theorem brouwer_fixedPoint_compactConvex
    {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS_ne : S.Nonempty) (hS_comp : IsCompact S) (hS_conv : Convex ℝ S)
    {T : (Fin n → ℝ) → (Fin n → ℝ)}
    (hT_cont : ContinuousOn T S) (hT_maps : Set.MapsTo T S S) :
    ∃ x ∈ S, T x = x := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  let S' : Set (EuclideanSpace ℝ (Fin n)) := e ⁻¹' S
  let T' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => e.symm (T (e x))
  have hS'_ne : S'.Nonempty := by
    obtain ⟨x, hx⟩ := hS_ne
    exact ⟨e.symm x, by simpa [S'] using hx⟩
  have hS'_comp : IsCompact S' := by
    rw [show S' = e.symm '' S by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [S'] using hy]
    exact hS_comp.image e.symm.continuous
  have hS'_conv : Convex ℝ S' := by
    exact hS_conv.linear_preimage e.toLinearMap
  have he_maps : Set.MapsTo e S' S := by
    intro x hx
    exact hx
  have hT'_cont : ContinuousOn T' S' := by
    have hcomp : ContinuousOn (fun x => T (e x)) S' :=
      hT_cont.comp e.continuous.continuousOn he_maps
    exact e.symm.continuous.comp_continuousOn hcomp
  have hT'_maps : Set.MapsTo T' S' S' := by
    intro x hx
    change e (e.symm (T (e x))) ∈ S
    simpa using hT_maps hx
  obtain ⟨x, hx, hfixed⟩ :=
    fixedPoint_of_compact_convex hS'_ne hS'_comp hS'_conv hT'_cont hT'_maps
  refine ⟨e x, hx, ?_⟩
  apply e.symm.injective
  simpa [T'] using hfixed
