/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalPhaseApprox
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Matrix.Normed

/-!
# Limits of spectral functions and of the phase rate

This file collects the limit statements used to pass from faithful to singular states in
the marginal-phase comparison.

* Spectral functions in a fixed eigenbasis converge when their eigenvalue functions do.
* A phase family whose values on the kernel are a common unimodular scalar, applied to
  a convergent family annihilated in the limit by the kernel projection, converges to
  the kernel-completed phase applied to the limit.
* The rate `𝓡_η` is continuous in `η ≥ 0`, including at `η = 0`.

## Main results

* `Matrix.tendsto_spectralFun`.
* `Matrix.tendsto_lift_spectralFun_mul`.
* `Matrix.tendsto_phaseRate`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 456–478.
-/

open Filter Topology
open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem continuous_spectralFun (U : unitary (Matrix n n ℂ)) :
    Continuous fun f : n → ℂ => spectralFun U f := by
  unfold spectralFun
  fun_prop

theorem tendsto_spectralFun (U : unitary (Matrix n n ℂ)) {ι : Type*} {l : Filter ι}
    {f : ι → n → ℂ} {g : n → ℂ} (h : ∀ k, Tendsto (fun e => f e k) l (𝓝 (g k))) :
    Tendsto (fun e => spectralFun U (f e)) l (𝓝 (spectralFun U g)) :=
  ((continuous_spectralFun U).tendsto g).comp (tendsto_pi_nhds.2 h)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- **Phases on a converging family.**  Let `qₑ` be eigenvalue functions converging to `p`
off the kernel and equal on the kernel to a common unimodular scalar `cₑ`.  If `Yₑ → Y₀`
and the lifted kernel projection annihilates `Y₀`, then
`L(spectralFun U qₑ) Yₑ → L(M̂) Y₀`, where `M̂` takes the value `1` on the kernel. -/
theorem tendsto_lift_spectralFun_mul (U : unitary (Matrix n n ℂ)) (lam : n → ℝ)
    {ι : Type*} {l : Filter ι} (q : ι → n → ℂ) (p : n → ℂ) (c : ι → ℂ)
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (Y : ι → Matrix m m ℂ) (Y₀ : Matrix m m ℂ)
    (hq : ∀ k, lam k ≠ 0 → Tendsto (fun e => q e k) l (𝓝 (p k)))
    (hqc : ∀ e k, lam k = 0 → q e k = c e) (hc : ∀ e, ‖c e‖ = 1)
    (hY : Tendsto Y l (𝓝 Y₀))
    (hK : L (spectralFun U (fun k => if lam k = 0 then 1 else 0)) * Y₀ = 0) :
    Tendsto (fun e => L (spectralFun U (q e)) * Y e) l
      (𝓝 (L (spectralFun U (fun k => if lam k = 0 then 1 else p k)) * Y₀)) := by
  set K := spectralFun U (fun k => if lam k = 0 then (1 : ℂ) else 0)
  set A : ι → Matrix n n ℂ := fun e => spectralFun U (fun k => if lam k = 0 then 0 else q e k)
  set A₀ := spectralFun U (fun k => if lam k = 0 then (0 : ℂ) else p k)
  have hdecomp : ∀ e, spectralFun U (q e) = A e + c e • K := by
    intro e
    simp only [A, K, ← spectralFun_smul, ← spectralFun_add]
    congr 1; funext k
    by_cases h : lam k = 0 <;> simp [h, hqc e k]
  have hhat : spectralFun U (fun k => if lam k = 0 then 1 else p k) = A₀ + K := by
    simp only [A₀, K, ← spectralFun_add]
    congr 1; funext k
    by_cases h : lam k = 0 <;> simp [h]
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hA : Tendsto A l (𝓝 A₀) := tendsto_spectralFun U fun k => by
    by_cases h : lam k = 0
    · simp only [h, ite_true]; exact tendsto_const_nhds
    · simp only [h, ite_false]; exact hq k h
  have h1 : Tendsto (fun e => L (A e) * Y e) l (𝓝 (L A₀ * Y₀)) :=
    ((hLc.tendsto A₀).comp hA).mul hY
  have h2 : Tendsto (fun e => c e • (L K * Y e)) l (𝓝 0) := by
    have h3 : Tendsto (fun e => L K * Y e) l (𝓝 (L K * Y₀)) := tendsto_const_nhds.mul hY
    rw [hK] at h3
    refine squeeze_zero_norm (fun e => ?_) (tendsto_zero_iff_norm_tendsto_zero.1 h3)
    rw [norm_smul, hc e, one_mul]
  have h4 := h1.add h2
  rw [add_zero] at h4
  rw [hhat, map_add, Matrix.add_mul, hK, add_zero]
  refine h4.congr fun e => ?_
  rw [hdecomp, map_add, map_smul, Matrix.add_mul, Matrix.smul_mul]

/-- The rate `𝓡` is bounded near zero by a continuous function vanishing at zero. -/
theorem phaseRate_le_of_lt_one {D x : ℝ} (hD : 1 ≤ D) (hx : x < 1) :
    phaseRate D x ≤ √(max x 0) + √(max x 0 * (1 + Real.log D) + Real.negMulLog (max x 0)) := by
  unfold phaseRate
  split_ifs with h
  · rw [max_eq_left h.le, min_eq_right hx.le]
    gcongr
    rw [Real.log_div (by positivity) h.ne', Real.log_mul (Real.exp_pos 1).ne' (by linarith),
      Real.log_exp, Real.negMulLog]
    ring_nf
    rfl
  · positivity

theorem tendsto_phaseRate {D : ℝ} (hD : 1 ≤ D) {ι : Type*} {l : Filter ι} {η : ι → ℝ} {η₀ : ℝ}
    (hη : Tendsto η l (𝓝 η₀)) (hη₀ : 0 ≤ η₀) :
    Tendsto (fun e => phaseRate D (η e)) l (𝓝 (phaseRate D η₀)) := by
  rcases hη₀.lt_or_eq with hpos | hzero
  · have hev : ∀ᶠ e in l, 0 < η e := hη.eventually (lt_mem_nhds hpos)
    have hcont : ContinuousAt (fun x : ℝ =>
        √(min 1 x) + √(x * Real.log (Real.exp 1 * D / min 1 x))) η₀ := by
      have hmin : 0 < min 1 η₀ := lt_min one_pos hpos
      refine ContinuousAt.add (Real.continuous_sqrt.continuousAt.comp ?_) ?_
      · exact (continuous_const.min continuous_id).continuousAt
      · refine Real.continuous_sqrt.continuousAt.comp (ContinuousAt.mul continuousAt_id ?_)
        refine ContinuousAt.log (continuousAt_const.div
          (continuous_const.min continuous_id).continuousAt hmin.ne') ?_
        have : 0 < D := by linarith
        positivity
    have := hcont.tendsto.comp hη
    rw [show phaseRate D η₀ = √(min 1 η₀) + √(η₀ * Real.log (Real.exp 1 * D / min 1 η₀)) by
      simp only [phaseRate, hpos, ↓reduceIte]]
    refine this.congr' ?_
    filter_upwards [hev] with e he
    simp only [phaseRate, he, ↓reduceIte, Function.comp]
  · subst hzero
    rw [show phaseRate D 0 = 0 by simp [phaseRate]]
    set g : ℝ → ℝ := fun x => √(max x 0) + √(max x 0 * (1 + Real.log D) + Real.negMulLog (max x 0))
    have hg : Continuous g := by
      unfold g
      have := Real.continuous_negMulLog
      fun_prop
    have hg0 : g 0 = 0 := by simp [g]
    have hlim : Tendsto (fun e => g (η e)) l (𝓝 0) := by
      rw [← hg0]; exact (hg.tendsto 0).comp hη
    have hev : ∀ᶠ e in l, η e < 1 := hη.eventually (gt_mem_nhds one_pos)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards with e
      unfold phaseRate; split_ifs <;> positivity
    · filter_upwards [hev] with e he
      exact phaseRate_le_of_lt_one hD he

end Matrix

end
