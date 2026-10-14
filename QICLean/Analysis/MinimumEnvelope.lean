/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.Bounds.Defs
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz continuity of an attained minimum

An attained minimum of real-valued functions with a common Lipschitz constant
has the same Lipschitz constant. The feasible parameter set requires no topology,
and the minimizers need not be uniquely determined or vary continuously.

This is a scalar supporting lemma for OpenAI, *Polynomial PEPS approximation of
gapped square-grid ground states*, September 24, 2026, `03-patches.tex`,
lines 421–481, in particular `eq:patch-uniform-local-lipschitz`.
It does not establish the derivative bound for the matrix-valued filter family.
-/

open Set Filter
open scoped NNReal Topology

/-- An attained minimum inherits the common Lipschitz constant of its branches.
Source: OpenAI `03-patches.tex`, lines 421–451. -/
theorem lipschitzOnWith_of_isLeast {X ι : Type*} [PseudoMetricSpace X]
    {f : X → ι → ℝ} {g : X → ℝ} {S : Set ι} {J : Set X} {C : ℝ≥0}
    (hmin : ∀ t ∈ J, IsLeast (f t '' S) (g t))
    (hbranch : ∀ x ∈ S, LipschitzOnWith C (fun t ↦ f t x) J) :
    LipschitzOnWith C g J :=
  LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦
    have hbound : ∀ u ∈ J, ∀ v ∈ J, g u - g v ≤ (C : ℝ) * dist u v :=
      fun u hu v hv ↦
        match (hmin v hv).1 with
        | ⟨x, hx, heq⟩ =>
          calc
            g u - g v ≤ f u x - g v :=
              sub_le_sub_right ((hmin u hu).2 (mem_image_of_mem (f u) hx)) _
            _ = f u x - f v x := congrArg (fun z ↦ f u x - z) heq.symm
            _ ≤ |f u x - f v x| := le_abs_self _
            _ = dist (f u x) (f v x) := (Real.dist_eq _ _).symm
            _ ≤ (C : ℝ) * dist u v := (hbranch x hx).dist_le_mul u hu v hv
    show |g s - g t| ≤ (C : ℝ) * dist s t from
      abs_sub_le_iff.mpr
        ⟨hbound s hs t ht,
          (hbound t ht s hs).trans_eq
            (congrArg (fun d : ℝ ↦ (C : ℝ) * d) (dist_comm t s))⟩

/-- A continuous lower envelope with contacting right-differentiable branches
of derivative at most a fixed constant grows at most at that rate. No regularity
of a selection of contacting branches is required.
Source: OpenAI `03-patches.tex`, lines 453–481, `eq:patch-minimum-growth`. -/
theorem lower_envelope_le_affine_of_hasDerivWithinAt {ι : Type*}
    {f : ℝ → ι → ℝ} {g : ℝ → ℝ} {S : Set ι} {a b c : ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hle : ∀ t ∈ Icc a b, ∀ x ∈ S, g t ≤ f t x)
    (hcontact : ∀ t ∈ Ico a b, ∃ x ∈ S, ∃ d : ℝ,
      f t x = g t ∧ HasDerivWithinAt (fun z ↦ f z x) d (Ici t) t ∧ d ≤ c) :
    ∀ ⦃r⦄, r ∈ Icc a b → g r ≤ g a + c * (r - a) :=
  have hB : ∀ t, HasDerivAt (fun r : ℝ ↦ g a + c * (r - a)) c t :=
    fun t ↦ (mul_one c) ▸ (((hasDerivAt_id t).sub_const a).const_mul c).const_add (g a)
  have hBa : g a + c * (a - a) = g a :=
    calc
      g a + c * (a - a) = g a + c * 0 := congrArg (fun z ↦ g a + c * z) (sub_self a)
      _ = g a + 0 := congrArg (fun z ↦ g a + z) (mul_zero c)
      _ = g a := add_zero _
  image_le_of_liminf_slope_right_le_deriv_boundary
    (B := fun r ↦ g a + c * (r - a)) (B' := fun _ ↦ c)
    hg hBa.ge
    (continuous_iff_continuousAt.mpr (fun t ↦ (hB t).continuousAt)).continuousOn
    (fun t _ ↦ (hB t).hasDerivWithinAt)
    fun t ht q hq ↦
      match hcontact t ht with
      | ⟨x, hx, d, heq, hder, hd⟩ =>
        ((hder.liminf_right_slope_le (lt_of_le_of_lt hd hq)).and_eventually
          (Ioc_mem_nhdsGT ht.2)).mono fun z hz ↦
          have hcomp : g z - g t ≤ f z x - f t x :=
            calc
              g z - g t ≤ f z x - g t :=
                sub_le_sub_right (hle z ⟨ht.1.trans hz.2.1.le, hz.2.2⟩ x hx) _
              _ = f z x - f t x := congrArg (fun y ↦ f z x - y) heq.symm
          have hslope : slope g t z ≤ slope (fun r ↦ f r x) t z :=
            calc
              slope g t z = (g z - g t) / (z - t) := slope_def_field _ _ _
              _ ≤ (f z x - f t x) / (z - t) :=
                div_le_div_of_nonneg_right hcomp (sub_nonneg.mpr hz.2.1.le)
              _ = slope (fun r ↦ f r x) t z := (slope_def_field _ _ _).symm
          hslope.trans_lt hz.1
