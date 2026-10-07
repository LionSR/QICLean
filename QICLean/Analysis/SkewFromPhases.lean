/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StripQuadratic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Departure from the positive axis from phase control

Let `f` be an entire function with `f(-z̄) = conj f(z)`, bounded by one on the
imaginary axis and by `m ≥ 1` on the strip `|Re z| ≤ 1/4`, and suppose its values on
the imaginary axis stay close to `p = f 0 ≥ 0`:
`|f(iu) - p| ≤ 2 √p E(u) + E(u)²` with `E(u) = 2 |sinh π u| R`.  Then for small real
`t`, `|f t| - Re f t ≤ t² (8π² R² + K ℓ² √(min 1 R))` with a universal `K`, where
`log m ≤ 2ℓ`.  This is the analytic core of the conditional skew estimate.

## Main results

* `Complex.norm_sub_sub_deriv_le` — second-order Taylor remainder from a disk bound.
* `Complex.norm_sub_re_le_of_phase_bounds` — the departure bound.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.3
  (`lem:skew`), `04-conditional.tex`, lines 562–600.
-/

open Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Complex

/-- **Second-order Taylor remainder.** An entire function bounded by `M` on the closed
disk of radius `δ` satisfies `‖g t - g 0 - t g'(0)‖ ≤ 3 M ‖t‖² / δ²` on that disk. -/
theorem norm_sub_sub_deriv_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {M δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ z ∈ closedBall (0 : ℂ) δ, ‖g z‖ ≤ M) {t : ℂ} (ht : ‖t‖ ≤ δ) :
    ‖g t - g 0 - t * deriv g 0‖ ≤ 3 * M * ‖t‖ ^ 2 / δ ^ 2 := by
  set k : ℂ → ℂ := fun w ↦ g w - g 0 - w * deriv g 0 with hk_def
  have hk : Differentiable ℂ k :=
    (hg.sub (differentiable_const _)).sub (differentiable_id.mul (differentiable_const _))
  have hk0 : k 0 = 0 := by simp [k]
  have hkd : deriv k 0 = 0 := by
    have h2 : HasDerivAt k (deriv g 0 - 0 - 1 * deriv g 0) 0 :=
      (((hg 0).hasDerivAt.sub (hasDerivAt_const _ _)).sub
        ((hasDerivAt_id 0).mul_const (deriv g 0)))
    simpa using h2.deriv
  set q : ℂ → ℂ := dslope (dslope k 0) 0 with hq_def
  have hk1 : Differentiable ℂ (dslope k 0) := fun w ↦
    ((differentiableOn_dslope (s := univ) Filter.univ_mem).mpr hk.differentiableOn).differentiableAt
      Filter.univ_mem
  have hq : Differentiable ℂ q := fun w ↦
    ((differentiableOn_dslope (s := univ) Filter.univ_mem).mpr
      hk1.differentiableOn).differentiableAt Filter.univ_mem
  have hkq : ∀ w, k w = w ^ 2 * q w := by
    intro w
    have e1 := sub_smul_dslope k 0 w
    have e2 := sub_smul_dslope (dslope k 0) 0 w
    rw [dslope_same, hkd, hk0] at *
    simp only [sub_zero, smul_eq_mul] at e1 e2
    rw [← e1, ← e2]; ring
  have hgd : ‖deriv g 0‖ ≤ M / δ :=
    norm_deriv_le_of_forall_mem_sphere_norm_le hδ hg.diffContOnCl
      fun z hz ↦ hM z (sphere_subset_closedBall hz)
  have hkb : ∀ w ∈ sphere (0 : ℂ) δ, ‖k w‖ ≤ 3 * M := by
    intro w hw
    have hwn : ‖w‖ = δ := by simpa using hw
    have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) δ := mem_closedBall_self hδ.le
    calc ‖k w‖ ≤ ‖g w‖ + ‖g 0‖ + ‖w * deriv g 0‖ :=
          norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ M + M + δ * (M / δ) := by
          gcongr
          · exact hM w (sphere_subset_closedBall hw)
          · exact hM 0 h0
          · rw [norm_mul, hwn]; exact mul_le_mul_of_nonneg_left hgd hδ.le
      _ = 3 * M := by field_simp; ring
  have hqb : ∀ w ∈ closedBall (0 : ℂ) δ, ‖q w‖ ≤ 3 * M / δ ^ 2 := by
    intro w hw
    rw [← closure_ball (0 : ℂ) hδ.ne'] at hw
    refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball hq.diffContOnCl ?_ hw
    intro v hv
    rw [frontier_ball (0 : ℂ) hδ.ne'] at hv
    have hvn : ‖v‖ = δ := by simpa using hv
    have hkv := hkb v hv
    rw [hkq v, norm_mul, norm_pow, hvn] at hkv
    rw [le_div_iff₀ (by positivity)]
    linarith [mul_comm (δ ^ 2) ‖q v‖]
  have htb : t ∈ closedBall (0 : ℂ) δ := by simpa using ht
  calc ‖g t - g 0 - t * deriv g 0‖ = ‖k t‖ := rfl
    _ = ‖t‖ ^ 2 * ‖q t‖ := by rw [hkq, norm_mul, norm_pow]
    _ ≤ ‖t‖ ^ 2 * (3 * M / δ ^ 2) := mul_le_mul_of_nonneg_left (hqb t htb) (by positivity)
    _ = 3 * M * ‖t‖ ^ 2 / δ ^ 2 := by ring

end Complex

end
