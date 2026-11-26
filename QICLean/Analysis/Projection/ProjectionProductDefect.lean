/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Order.Field

/-!
# Defects of products of orthogonal projections

For closed subspaces `U`, `V`, `W` the defect `P_U P_V - P_W` measures how far the product of two
orthogonal projections is from a third.

An isometric change of coordinates conjugates orthogonal projections and preserves operator norms,
and the adjoint reverses the order of the two projections: a defect `P_U P_V - P_W` in one
coordinate system has the norm of `P_W - P_V P_U` in the original coordinates.

If `U`, `V`, `W` have sector subspaces `S i`, `T i`, `C i` and each joint projection is
approximated by the sum of its sector projections, the joint defect is bounded by the three
approximation errors and the finite sum of the sector defects: `P_{S i} P_{T i} - P_{C i}` on the
diagonal and `P_{S i} P_{T j}` off it. Sector orthogonality is not assumed. The resulting norm
convergence statement allows the Hilbert spaces to vary and the filter to be arbitrary.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531, and
Lemma disjoint, lines 1744--1820.

Moved from TNLean, `TNLean/Algebra/ProjectionDefectIsometry.lean` and
`TNLean/Algebra/SectorProjectionSumDefect.lean` at commit `49b78ed821` (Apache-2.0). Changes:
the two files are merged; docstrings rewritten.

## Main results

* `Submodule.norm_map_starProjection_comp_sub_eq`
* `Submodule.norm_starProjection_comp_sub_le_sector_errors`
* `Submodule.tendsto_norm_starProjection_comp_sub_zero_of_sector_errors`

Moved from TNLean,
`TNLean/MPS/ParentHamiltonian/ProjectorDefect/DimensionConstant/ProjectorWitness.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open scoped BigOperators

namespace Submodule
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Isometric transport preserves the norm of a three-projection defect;
taking the adjoint reverses the projection order. Source: the coordinate
transport used in Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. No finite-dimensional hypothesis is required. -/
theorem norm_map_starProjection_comp_sub_eq
    (e : E ≃ₗᵢ[𝕜] F) (U V W : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    ‖(U.map e.toLinearMap).starProjection.comp (V.map e.toLinearMap).starProjection -
      (W.map e.toLinearMap).starProjection‖ =
      ‖W.starProjection - V.starProjection.comp U.starProjection‖ := by
  have hConj :
      (U.map e.toLinearMap).starProjection.comp (V.map e.toLinearMap).starProjection -
        (W.map e.toLinearMap).starProjection =
      (e : E →L[𝕜] F).comp
        ((U.starProjection.comp V.starProjection - W.starProjection).comp
          (e.symm : F →L[𝕜] E)) := by
    ext x
    simp only [sub_apply, ContinuousLinearMap.comp_apply, starProjection_map_apply,
      LinearIsometryEquiv.symm_apply_apply, map_sub]
    rfl
  rw [hConj, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  change ‖U.starProjection * V.starProjection - W.starProjection‖ =
    ‖W.starProjection - V.starProjection * U.starProjection‖
  rw [← norm_star, star_sub, star_mul, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq,
    norm_sub_rev]

end Submodule

namespace Submodule

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι] [DecidableEq ι]

/-- The joint projection defect is controlled by projection-sum errors,
paired sector defects, and cross-sector overlaps. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem norm_starProjection_comp_sub_le_sector_errors
    (U V W : Submodule 𝕜 E) (S T C : ι → Submodule 𝕜 E) :
    ‖U.starProjection.comp V.starProjection - W.starProjection‖ ≤
      ‖U.starProjection - ∑ i, (S i).starProjection‖ +
      (Fintype.card ι : ℝ) * ‖V.starProjection - ∑ i, (T i).starProjection‖ +
      (∑ i, ∑ j, ‖(S i).starProjection.comp (T j).starProjection -
        (if i = j then (C i).starProjection else 0)‖) +
      ‖(∑ i, (C i).starProjection) - W.starProjection‖ := by
  classical
  let P := ∑ i, (S i).starProjection
  let Q := ∑ i, (T i).starProjection
  let Z := ∑ i, (C i).starProjection
  have hSum : (∑ i, ∑ j, ((S i).starProjection * (T j).starProjection -
      (if i = j then (C i).starProjection else 0))) = P * Q - Z := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, P, Q, Z]
  have hP : ‖P‖ ≤ (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ i, ‖(S i).starProjection‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (S i).starProjection_norm_le
      _ = _ := by simp
  have hFirst : ‖(U.starProjection - P) * V.starProjection‖ ≤ ‖U.starProjection - P‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left V.starProjection_norm_le
      (norm_nonneg _)).trans_eq (mul_one _))
  have hSecond : ‖P * (V.starProjection - Q)‖ ≤
      (Fintype.card ι : ℝ) * ‖V.starProjection - Q‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hMiddle : ‖P * Q - Z‖ ≤
      ∑ i, ∑ j, ‖(S i).starProjection * (T j).starProjection -
        (if i = j then (C i).starProjection else 0)‖ := by
    rw [← hSum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have hAlg : U.starProjection * V.starProjection - W.starProjection =
      ((U.starProjection - P) * V.starProjection + P * (V.starProjection - Q)) +
        (P * Q - Z) + (Z - W.starProjection) := by noncomm_ring
  change ‖U.starProjection * V.starProjection - W.starProjection‖ ≤ _
  rw [hAlg]
  calc
    _ ≤ ‖(U.starProjection - P) * V.starProjection‖ +
        ‖P * (V.starProjection - Q)‖ + ‖P * Q - Z‖ + ‖Z - W.starProjection‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hFirst hSecond) hMiddle) le_rfl

omit [DecidableEq ι] in
/-- Vanishing sector defects and projection-sum errors imply vanishing
joint projection defect. The ambient Hilbert spaces may vary with the index.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531, and Lemma disjoint, lines 1744--1820. The corresponding
sectorwise estimates are explicit hypotheses. -/
theorem tendsto_norm_starProjection_comp_sub_zero_of_sector_errors
    {α : Type*} {f : Filter α} {F : α → Type*}
    [∀ a, NormedAddCommGroup (F a)] [∀ a, InnerProductSpace 𝕜 (F a)]
    [∀ a, FiniteDimensional 𝕜 (F a)]
    (U V W : (a : α) → Submodule 𝕜 (F a))
    (S T C : (a : α) → ι → Submodule 𝕜 (F a))
    (hU : Filter.Tendsto (fun a =>
      ‖(U a).starProjection - ∑ i, (S a i).starProjection‖) f (nhds 0))
    (hV : Filter.Tendsto (fun a =>
      ‖(V a).starProjection - ∑ i, (T a i).starProjection‖) f (nhds 0))
    (hW : Filter.Tendsto (fun a =>
      ‖(∑ i, (C a i).starProjection) - (W a).starProjection‖) f (nhds 0))
    (hDiag : ∀ i, Filter.Tendsto (fun a =>
      ‖(S a i).starProjection.comp (T a i).starProjection - (C a i).starProjection‖)
      f (nhds 0))
    (hCross : ∀ i j, i ≠ j → Filter.Tendsto (fun a =>
      ‖(S a i).starProjection.comp (T a j).starProjection‖) f (nhds 0)) :
    Filter.Tendsto (fun a =>
      ‖(U a).starProjection.comp (V a).starProjection - (W a).starProjection‖)
      f (nhds 0) := by
  classical
  have hTerm (i j : ι) : Filter.Tendsto (fun a =>
      ‖(S a i).starProjection.comp (T a j).starProjection -
        (if i = j then (C a i).starProjection else 0)‖) f (nhds 0) := by
    by_cases hij : i = j
    · simpa only [hij, ite_true] using hDiag j
    · simpa only [ite_eq_right hij, sub_zero] using hCross i j hij
  have hSum : Filter.Tendsto (fun a =>
      ∑ i, ∑ j, ‖(S a i).starProjection.comp (T a j).starProjection -
        (if i = j then (C a i).starProjection else 0)‖) f (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ =>
        tendsto_finsetSum Finset.univ (fun j _ => hTerm i j))
  have hUpper : Filter.Tendsto (fun a =>
      ‖(U a).starProjection - ∑ i, (S a i).starProjection‖ +
      (Fintype.card ι : ℝ) * ‖(V a).starProjection - ∑ i, (T a i).starProjection‖ +
      (∑ i, ∑ j, ‖(S a i).starProjection.comp (T a j).starProjection -
        (if i = j then (C a i).starProjection else 0)‖) +
      ‖(∑ i, (C a i).starProjection) - (W a).starProjection‖) f (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      ((hU.add (hV.const_mul (Fintype.card ι : ℝ))).add hSum).add hW
  exact squeeze_zero' (Filter.Eventually.of_forall fun a => norm_nonneg _)
    (Filter.Eventually.of_forall fun a =>
      norm_starProjection_comp_sub_le_sector_errors (U a) (V a) (W a) (S a) (T a) (C a))
    hUpper

end Submodule

section

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unit witnesses bound a projection defect from below by their inner product. -/
theorem norm_inner_le_norm_projection_defect
    (U V W : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {x y : E} (hx : x ∈ V) (hy : y ∈ U) (hxW : x ∈ Wᗮ)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ‖inner ℂ y x‖ ≤ ‖U.starProjection.comp V.starProjection - W.starProjection‖ := by
  have hinner : inner ℂ y
      ((U.starProjection.comp V.starProjection - W.starProjection) x) = inner ℂ y x := by
    simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.comp_apply,
      V.starProjection_eq_self_iff.mpr hx, W.starProjection_apply_eq_zero_iff.mpr hxW,
      sub_zero, ← U.inner_starProjection_left_eq_right,
      U.starProjection_eq_self_iff.mpr hy]
  exact (show ‖inner ℂ y x‖ ≤
      ‖(U.starProjection.comp V.starProjection - W.starProjection) x‖ from
    by simpa only [hinner, hny, one_mul] using
      norm_inner_le_norm (𝕜 := ℂ) y
        ((U.starProjection.comp V.starProjection - W.starProjection) x)).trans
      (by simpa only [hnx, mul_one] using
        (U.starProjection.comp V.starProjection - W.starProjection).le_opNorm x)

/-- The same witnesses bound the defect with the two projections reversed. -/
theorem norm_inner_le_norm_projection_defect_reverse [CompleteSpace E]
    (U V W : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {x y : E} (hx : x ∈ V) (hy : y ∈ U) (hxW : x ∈ Wᗮ)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ‖inner ℂ y x‖ ≤ ‖V.starProjection.comp U.starProjection - W.starProjection‖ := by
  have h := norm_inner_le_norm_projection_defect U V W hx hy hxW hnx hny
  simpa only [← ContinuousLinearMap.mul_def, star_sub, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq] using
    h.trans_eq (norm_star (U.starProjection * V.starProjection - W.starProjection)).symm

end Submodule

end
