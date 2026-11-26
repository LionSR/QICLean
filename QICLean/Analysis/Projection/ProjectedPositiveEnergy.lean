/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import QICLean.Analysis.Subspace.ViableSubspace
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Positive energy after projection into a close space

The regional energy-estimation step in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1631–1632, and proof of `t:alg1`, lines 1805–1806,
uses a low-energy vector projected into a viable space. A positive regional
operator need not annihilate the original global ground space. Its original
quadratic-form bound and the projection loss still give an explicit energy
bound. The estimates below concern the actual orthogonal projection.

It also contains the following results.

* `Submodule.IsCloseTo.map_starProjection_energy_le`: the energy of a projected trial space.
* `ContinuousLinearMap.re_inner_apply_le_mul_norm_sq`,
  `Submodule.IsCloseTo.norm_sub_starProjection_sq_le`: projection loss and quadratic-form norm
  bounds.
-/

open scoped InnerProductSpace

section QuadraticBounds

/-!
## Projection loss and quadratic-form norm bounds

Pythagoras converts closeness into a squared projection-error bound.
Cauchy--Schwarz controls a bounded operator's quadratic form by its norm.
These estimates are shared by projected trial energy and regional-energy
arguments in ALVV, arXiv:1602.08828v2, Lemma `l:close`, lines 484–489,
and Figure `fig:algo1`, lines 1631–1632.
-/

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A bounded operator's real quadratic form is controlled by any upper
bound for its operator norm. This is the Cauchy--Schwarz estimate used
in ALVV's energy-estimation step, arXiv:1602.08828v2, line 1631. -/
theorem re_inner_apply_le_mul_norm_sq (H : E →L[𝕜] E) {A : ℝ}
    (hA : ‖H‖ ≤ A) (x : E) : RCLike.re ⟪H x, x⟫_𝕜 ≤ A * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖H x‖ * ‖x‖ := re_inner_le_norm _ _
    _ ≤ (A * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        ((H.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))) (norm_nonneg x)
    _ = _ := by ring

end ContinuousLinearMap

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Closeness bounds the squared distance to the actual orthogonal projection.
No supplied approximating vector or nonzero-target premise is needed.
Auxiliary to ALVV, arXiv:1602.08828v2, Lemma `l:close`, lines 484–489. -/
theorem IsCloseTo.norm_sub_starProjection_sq_le {delta : ℝ}
    {S T : Submodule 𝕜 E} (h : IsCloseTo delta S T) {x : E} (hx : x ∈ T) :
    ‖x - S.starProjection x‖ ^ 2 ≤ delta * ‖x‖ ^ 2 := by
  have hp := norm_sq_eq_add_norm_sq_starProjection x S
  rw [starProjection_orthogonal_val] at hp
  nlinarith only [hp, (isCloseTo_iff.mp h) x hx]

end Submodule

end QuadraticBounds

section ProjectedPositiveEnergy

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A weighted bound for a positive quadratic form at a sum. It follows
by evaluating the form at the difference with the second vector multiplied
by a positive real weight. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1631–1632. -/
theorem IsPositive.re_inner_add_le_weighted {H : E →L[𝕜] E}
    (hH : H.IsPositive) (x y : E) {r : ℝ} (hr : 0 < r) :
    RCLike.re ⟪H (x + y), x + y⟫_𝕜 ≤
      (1 + 1 / r) * RCLike.re ⟪H x, x⟫_𝕜 +
        (1 + r) * RCLike.re ⟪H y, y⟫_𝕜 := by
  have hdiff := hH.re_inner_nonneg_left (x - (r : 𝕜) • y)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul] at hdiff
  calc
    _ ≤ ((r + 1) * RCLike.re ⟪H x, x⟫_𝕜 +
        r * (r + 1) * RCLike.re ⟪H y, y⟫_𝕜) / r := by
      apply (le_div_iff₀ hr).mpr
      simp only [map_add, inner_add_left, inner_add_right]
      nlinarith only [hdiff]
    _ = _ := by field_simp [hr.ne']; ring

end ContinuousLinearMap

namespace Real

/-- A small projection loss keeps a regional energy initially at most two
below three after normalization. This is a numerical auxiliary for ALVV,
arXiv:1602.08828v2, the energy-estimation step in Figure `fig:algo1`,
lines 1631–1632. -/
theorem projected_positive_energy_le_three {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (100 * (A + 1))) :
    δ < 1 ∧ (9 / 4 + 9 * A * δ) / (1 - δ) ≤ 3 := by
  have hmul : δ * (100 * (A + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 100 * (A + 1))).mp hsmall
  have hδ1 : δ < 1 := by nlinarith only [hmul, mul_nonneg hA hδ]
  refine ⟨hδ1, (div_le_iff₀ (by linarith only [hδ1] : 0 < 1 - δ)).mpr ?_⟩
  nlinarith only [hmul, hδ, mul_nonneg hA hδ]

end Real

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The actual projected target space has bounded positive energy when the
original target has bounded positive energy. In contrast to the zero-energy
case, the regional operator need not annihilate the global ground space.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632,
and proof of `t:alg1`, lines 1805–1806. -/
theorem IsCloseTo.map_starProjection_positive_energy_le {δ E0 A : ℝ}
    {U G : Submodule 𝕜 E} (h : IsCloseTo δ U G) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (r : ℝ) (hr : 0 < r) (H : E →L[𝕜] E) (hH : H.IsPositive) (hE0 : 0 ≤ E0)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ E0 * ‖g‖ ^ 2) (hA : ‖H‖ ≤ A) :
    ∀ x ∈ G.map U.starProjection.toLinearMap,
      RCLike.re ⟪H x, x⟫_𝕜 ≤ ((1 + 1 / r) * E0 + (1 + r) * A * δ) / (1 - δ) * ‖x‖ ^ 2 := by
  rintro x ⟨g, hg, rfl⟩
  change RCLike.re ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 ≤
    ((1 + 1 / r) * E0 + (1 + r) * A * δ) / (1 - δ) * ‖U.starProjection g‖ ^ 2
  have hc : 0 < 1 - δ := by linarith only [hδ]
  have hA0 : 0 ≤ A := (norm_nonneg H).trans hA
  have hlow := (isCloseTo_iff.mp h) g hg
  have hdist : ‖U.starProjection g - g‖ ^ 2 ≤ δ * ‖g‖ ^ 2 := by
    simpa only [norm_sub_rev] using h.norm_sub_starProjection_sq_le hg
  have hdiffEnergy : RCLike.re ⟪H (U.starProjection g - g), U.starProjection g - g⟫_𝕜 ≤
      A * δ * ‖g‖ ^ 2 := by
    calc
      _ ≤ A * ‖U.starProjection g - g‖ ^ 2 :=
        H.re_inner_apply_le_mul_norm_sq hA _
      _ ≤ A * (δ * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_left hdist hA0
      _ = _ := by ring
  have henergy : RCLike.re ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 ≤
      ((1 + 1 / r) * E0 + (1 + r) * A * δ) * ‖g‖ ^ 2 := by
    calc
      _ ≤ (1 + 1 / r) * RCLike.re ⟪H g, g⟫_𝕜 +
          (1 + r) * RCLike.re ⟪H (U.starProjection g - g), U.starProjection g - g⟫_𝕜 := by
        simpa only [add_sub_cancel] using
          hH.re_inner_add_le_weighted g (U.starProjection g - g) hr
      _ ≤ (1 + 1 / r) * (E0 * ‖g‖ ^ 2) + (1 + r) * (A * δ * ‖g‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hG g hg) (by positivity))
          (mul_le_mul_of_nonneg_left hdiffEnergy (by positivity))
      _ = _ := by ring
  have hnorm : ‖g‖ ^ 2 ≤ ‖U.starProjection g‖ ^ 2 / (1 - δ) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlow)
  calc
    _ ≤ ((1 + 1 / r) * E0 + (1 + r) * A * δ) * ‖g‖ ^ 2 := henergy
    _ ≤ ((1 + 1 / r) * E0 + (1 + r) * A * δ) * (‖U.starProjection g‖ ^ 2 / (1 - δ)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- A candidate with projection loss at most the displayed inverse-norm
scale has regional energy at most three on the actual projected target
space, provided the original regional energy is at most two. This is an
auxiliary for ALVV, arXiv:1602.08828v2, the energy-estimation step in
Figure `fig:algo1`, lines 1631–1632. -/
theorem IsCloseTo.map_starProjection_energy_le_three {δ A : ℝ}
    {U G : Submodule 𝕜 E} (h : IsCloseTo δ U G) (hδ0 : 0 ≤ δ)
    (H : E →L[𝕜] E) (hH : H.IsPositive)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ 2 * ‖g‖ ^ 2)
    (hA : ‖H‖ ≤ A) (hsmall : δ ≤ 1 / (100 * (A + 1))) :
    ∀ x ∈ G.map U.starProjection.toLinearMap,
      RCLike.re ⟪H x, x⟫_𝕜 ≤ 3 * ‖x‖ ^ 2 := by
  have hnum := Real.projected_positive_energy_le_three ((norm_nonneg H).trans hA) hδ0 hsmall
  have hraw := h.map_starProjection_positive_energy_le hδ0 hnum.1 8 (by norm_num)
    H hH (by norm_num) hG hA
  norm_num only at hraw
  intro x hx
  exact (hraw x hx).trans (mul_le_mul_of_nonneg_right hnum.2 (sq_nonneg ‖x‖))

end Submodule

section CloseSubspaceEnergyTransfer

/-!
# Positive energy on a nearby target space

A positive regional operator need not vanish on the original global ground
space. Its quadratic-form bound transfers to a nearby soft spectral space
by projecting the latter into the original space. The projection loss and
operator norm remain explicit. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisefficient`, lines 1360–1371, and the energy-estimation
argument in the proof of `t:alg1`, line 1807.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A bound for a positive quadratic form transfers from a subspace to a
nearby target. The actual projection into the first space supplies the
comparison vector; no approximating vector is assumed.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:aisefficient`,
lines 1360–1371, and the energy-estimation argument at line 1807. -/
theorem IsCloseTo.positive_energy_le {delta E0 A : ℝ}
    {G T : Submodule 𝕜 E} (h : IsCloseTo delta G T)
    (H : E →L[𝕜] E) (hH : H.IsPositive) (hE0 : 0 ≤ E0)
    (hG : ∀ g ∈ G, RCLike.re ⟪H g, g⟫_𝕜 ≤ E0 * ‖g‖ ^ 2) (hA : ‖H‖ ≤ A)
    (r : ℝ) (hr : 0 < r) :
    ∀ t ∈ T, RCLike.re ⟪H t, t⟫_𝕜 ≤
      ((1 + 1 / r) * E0 + (1 + r) * A * delta) * ‖t‖ ^ 2 := by
  intro t ht
  have hprojected : RCLike.re ⟪H (G.starProjection t), G.starProjection t⟫_𝕜 ≤
      E0 * ‖t‖ ^ 2 :=
    (hG _ (G.starProjection_apply_mem t)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (G.norm_starProjection_apply_le t) 2) hE0)
  have hdiff : RCLike.re ⟪H (t - G.starProjection t), t - G.starProjection t⟫_𝕜 ≤
      A * delta * ‖t‖ ^ 2 := by
    calc
      _ ≤ A * ‖t - G.starProjection t‖ ^ 2 := H.re_inner_apply_le_mul_norm_sq hA _
      _ ≤ A * (delta * ‖t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h.norm_sub_starProjection_sq_le ht)
          ((norm_nonneg H).trans hA)
      _ = _ := by ring
  calc
    _ ≤ (1 + 1 / r) * RCLike.re ⟪H (G.starProjection t), G.starProjection t⟫_𝕜 +
        (1 + r) * RCLike.re ⟪H (t - G.starProjection t), t - G.starProjection t⟫_𝕜 := by
      simpa only [add_sub_cancel] using
        hH.re_inner_add_le_weighted (G.starProjection t) (t - G.starProjection t) hr
    _ ≤ (1 + 1 / r) * (E0 * ‖t‖ ^ 2) + (1 + r) * (A * delta * ‖t‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hprojected (by positivity))
        (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring

end Submodule

end CloseSubspaceEnergyTransfer

end ProjectedPositiveEnergy

section ProjectedTrialSpaceEnergy

/-!
## The energy of a projected trial space

For the final spectral extraction in ALVV, arXiv:1602.08828v2,
Algorithm `t:alg1`, lines 1634–1640, a candidate space close to the full
ground space must supply a trial space of the same dimension. Projecting
the ground space into the candidate constructs that trial space directly.
The energy bound holds on its entire span.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Projecting a zero-energy target into a close candidate gives an actual trial
space of the same dimension, with a bound on every vector's energy. This is an
auxiliary for the compressed spectral extraction in ALVV, arXiv:1602.08828v2,
Algorithm `t:alg1`, lines 1634–1640. -/
theorem IsCloseTo.map_starProjection_energy_le {δ A : ℝ} {U G : Submodule 𝕜 E}
    (h : IsCloseTo δ U G) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (H : E →L[𝕜] E) (hH : H.toLinearMap.IsSymmetric)
    (hG : ∀ g ∈ G, H g = 0) (hA : ‖H‖ ≤ A) :
    G.map U.starProjection.toLinearMap ≤ U ∧
      Module.finrank 𝕜 (G.map U.starProjection.toLinearMap) = Module.finrank 𝕜 G ∧
      ∀ x ∈ G.map U.starProjection.toLinearMap,
        RCLike.re ⟪H x, x⟫_𝕜 ≤ A * δ / (1 - δ) * ‖x‖ ^ 2 := by
  have hc : 0 < 1 - δ := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg H).trans hA
  have hv := isCloseTo_iff.mp h
  let f : G →ₗ[𝕜] E := U.starProjection.toLinearMap.comp G.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    by_contra hne
    exact (h.starProjection_ne_zero hδ g.2 hne) hg
  have hupper (v : E) : RCLike.re ⟪H v, v⟫_𝕜 ≤ A * ‖v‖ ^ 2 :=
    H.re_inner_apply_le_mul_norm_sq hA v
  have hrange : f.range = G.map U.starProjection.toLinearMap := by
    change (U.starProjection.toLinearMap.comp G.subtype).range = _
    rw [LinearMap.range_comp, G.range_subtype]
  have hdim : Module.finrank 𝕜 (G.map U.starProjection.toLinearMap) = Module.finrank 𝕜 G :=
    (congrArg (fun P : Submodule 𝕜 E => Module.finrank 𝕜 P) hrange).symm.trans
      (LinearMap.finrank_range_of_inj hinj)
  simp only [← hrange]
  refine ⟨?_, hdim, ?_⟩
  · rintro x ⟨g, rfl⟩
    exact U.starProjection_apply_mem g
  · rintro x ⟨g, rfl⟩
    change RCLike.re ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 ≤ _
    have hlow := hv g g.2
    have hdist : ‖U.starProjection (g : E) - g‖ ^ 2 ≤ δ * ‖(g : E)‖ ^ 2 := by
      simpa only [norm_sub_rev] using h.norm_sub_starProjection_sq_le g.2
    have hdiff : ‖U.starProjection (g : E) - g‖ ^ 2 ≤
        δ / (1 - δ) * ‖U.starProjection (g : E)‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have hh := mul_le_mul_of_nonneg_right hdist hc.le
      have hl := mul_le_mul_of_nonneg_left hlow hδ0
      nlinarith
    have hzero : H (g : E) = 0 := hG g g.2
    have hcross : ⟪H (U.starProjection g), (g : E)⟫_𝕜 = 0 := by
      calc
        _ = ⟪U.starProjection g, H (g : E)⟫_𝕜 := hH _ _
        _ = 0 := by rw [hzero, inner_zero_right]
    have heq : ⟪H (U.starProjection (g : E) - g), U.starProjection (g : E) - g⟫_𝕜 =
        ⟪H (U.starProjection g), U.starProjection g⟫_𝕜 := by
      rw [map_sub, hzero, sub_zero, inner_sub_right, hcross, sub_zero]
    calc
      _ = RCLike.re ⟪H (U.starProjection (g : E) - g), U.starProjection (g : E) - g⟫_𝕜 :=
        congrArg RCLike.re heq.symm
      _ ≤ A * ‖U.starProjection (g : E) - g‖ ^ 2 := hupper _
      _ ≤ A * (δ / (1 - δ) * ‖U.starProjection (g : E)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff hA0
      _ = _ := by dsimp [f]; ring

end Submodule

end ProjectedTrialSpaceEnergy
