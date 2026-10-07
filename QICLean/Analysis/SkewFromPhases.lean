/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StripQuadratic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Star

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

theorem abs_sinh_le_exp_abs (x : ℝ) : |Real.sinh x| ≤ Real.exp |x| := by
  rw [Real.sinh_eq, abs_div, abs_two]
  have h1 : |Real.exp x - Real.exp (-x)| ≤ Real.exp x + Real.exp (-x) := by
    rw [abs_le]; constructor <;> linarith [Real.exp_pos x, Real.exp_pos (-x)]
  have h2 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.2 (le_abs_self x)
  have h3 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.2 (neg_le_abs x)
  linarith

/-- The Gaussian damps the phase error: for `R ≥ 0`,
`(4 |sinh π u| R + 4 sinh² (π u) R²) e^{-u²} ≤ 8 e^{π²} R` when `R ≤ 1`. -/
theorem phaseError_mul_exp_le {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1) (u : ℝ) :
    (4 * |Real.sinh (Real.pi * u)| * R + 4 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2) *
      Real.exp (-u ^ 2) ≤ 8 * Real.exp (Real.pi ^ 2) * R := by
  have hs := abs_sinh_le_exp_abs (Real.pi * u)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hs2 : Real.sinh (Real.pi * u) ^ 2 ≤ Real.exp (2 * (Real.pi * |u|)) := by
    rw [← sq_abs, show 2 * (Real.pi * |u|) = Real.pi * |u| + Real.pi * |u| by ring,
      Real.exp_add, sq]
    exact mul_le_mul hs hs (abs_nonneg _) (Real.exp_pos _).le
  have he1 : Real.exp (Real.pi * |u|) * Real.exp (-u ^ 2) ≤ Real.exp (Real.pi ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (|u| - Real.pi / 2), sq_abs u, Real.pi_pos]
  have he2 : Real.exp (2 * (Real.pi * |u|)) * Real.exp (-u ^ 2) ≤ Real.exp (Real.pi ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (|u| - Real.pi), sq_abs u]
  have hR2 : R ^ 2 ≤ R := by nlinarith
  have hE := Real.exp_pos (-u ^ 2)
  calc (4 * |Real.sinh (Real.pi * u)| * R + 4 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2) *
        Real.exp (-u ^ 2)
      = 4 * R * (|Real.sinh (Real.pi * u)| * Real.exp (-u ^ 2)) +
          4 * R ^ 2 * (Real.sinh (Real.pi * u) ^ 2 * Real.exp (-u ^ 2)) := by ring
    _ ≤ 4 * R * Real.exp (Real.pi ^ 2) + 4 * R * Real.exp (Real.pi ^ 2) := by
        gcongr
        · exact (mul_le_mul_of_nonneg_right hs hE.le).trans he1
        · exact (mul_le_mul_of_nonneg_right hs2 hE.le).trans he2
    _ = 8 * Real.exp (Real.pi ^ 2) * R := by ring

theorem tendsto_sinh_pi_mul_div :
    Tendsto (fun u : ℝ => Real.sinh (Real.pi * u) / u) (𝓝[≠] 0) (𝓝 Real.pi) := by
  have h : HasDerivAt (fun u : ℝ => Real.sinh (Real.pi * u)) (Real.cosh (Real.pi * 0) * Real.pi) 0 :=
    (Real.hasDerivAt_sinh _).comp 0 ((hasDerivAt_id 0).const_mul Real.pi |>.congr_deriv (by ring))
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [mul_zero, Real.cosh_zero, one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp [slope_def_field, div_eq_inv_mul]

/-- The derivative at the origin is controlled by the phase error:
`‖f'(0)‖ ≤ 4 π √p R`.  Area-law manuscript, `04-conditional.tex`, lines 568–572. -/
theorem norm_deriv_le_of_phase {f : ℂ → ℂ} (hf : Differentiable ℂ f) {p R : ℝ}
    (hphase : ∀ u : ℝ, ‖f (u * I) - f 0‖ ≤
      4 * √p * |Real.sinh (Real.pi * u)| * R + 4 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2) :
    ‖deriv f 0‖ ≤ 4 * Real.pi * √p * R := by
  set g : ℝ → ℂ := fun u => f (u * I)
  have hg : HasDerivAt g (deriv f 0 * I) 0 := by
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * I) I 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I
    have h2 : HasDerivAt f (deriv f 0) ((0 : ℝ) * I : ℂ) := by
      simpa using (hf 0).hasDerivAt
    exact h2.comp (0 : ℝ) h1
  have hslope := hasDerivAt_iff_tendsto_slope.1 hg
  have hnorm := hslope.norm
  rw [norm_mul, norm_I, mul_one] at hnorm
  -- the bound on the slopes
  set B : ℝ → ℝ := fun u => 4 * √p * |Real.sinh (Real.pi * u) / u| * R +
    4 * |Real.sinh (Real.pi * u) / u| * |Real.sinh (Real.pi * u)| * R ^ 2
  have hB : Tendsto B (𝓝[≠] 0) (𝓝 (4 * √p * |Real.pi| * R + 4 * |Real.pi| * |Real.sinh (Real.pi * 0)| * R ^ 2)) := by
    have h1 := tendsto_sinh_pi_mul_div.abs
    have h2 : Tendsto (fun u : ℝ => |Real.sinh (Real.pi * u)|) (𝓝[≠] 0)
        (𝓝 |Real.sinh (Real.pi * 0)|) :=
      ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).abs.tendsto 0).mono_left
        nhdsWithin_le_nhds
    exact ((tendsto_const_nhds.mul h1).mul tendsto_const_nhds).add
      (((tendsto_const_nhds.mul h1).mul h2).mul tendsto_const_nhds)
  simp only [mul_zero, Real.sinh_zero, abs_zero, abs_of_pos Real.pi_pos, zero_mul,
    add_zero] at hB
  rw [show 4 * Real.pi * √p * R = 4 * √p * Real.pi * R by ring]
  refine le_of_tendsto_of_tendsto hnorm hB ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := hu
  rw [slope_def_module, norm_smul, sub_zero, norm_inv, Real.norm_eq_abs]
  have h := hphase u
  simp only [g, Complex.ofReal_zero, zero_mul] at h ⊢
  calc |u|⁻¹ * ‖f (u * I) - f 0‖
      ≤ |u|⁻¹ * (4 * √p * |Real.sinh (Real.pi * u)| * R +
          4 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2) := by gcongr
    _ = B u := by
        simp only [B, abs_div]
        rw [← sq_abs (Real.sinh _)]
        field_simp

/-- The real part of the derivative at the origin vanishes under `f(-z̄) = conj f(z)`. -/
theorem re_deriv_eq_zero_of_symm {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsymm : ∀ z, f (-(conj z)) = conj (f z)) : (deriv f 0).re = 0 := by
  set D := deriv f 0
  have h1 : HasDerivAt (fun x : ℝ => f (-(x : ℂ))) (-D) 0 := by
    have hn : HasDerivAt (fun x : ℝ => -(x : ℂ)) (-1) 0 := by
      have := (hasDerivAt_neg (0 : ℝ)).ofReal_comp
      convert this using 1
      · funext x; push_cast; ring
      · simp
    have := ((hf (-((0 : ℝ) : ℂ))).hasDerivAt).comp (0 : ℝ) hn
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun x : ℝ => conj (f (x : ℂ))) (conj D) 0 := by
    have := ((hf ((0 : ℝ) : ℂ)).hasDerivAt).comp_ofReal
    have h3 := HasDerivAt.star this
    simpa using h3
  have heq : (fun x : ℝ => f (-(x : ℂ))) = fun x : ℝ => conj (f (x : ℂ)) := by
    funext x
    rw [← hsymm, Complex.conj_ofReal]
  rw [heq] at h1
  have := h1.unique h2
  have hre := congrArg Complex.re this
  simp only [neg_re, conj_re] at hre
  linarith

/-- **Departure from the positive axis.**  Let `f` be entire with `f(-z̄) = conj f(z)`,
`‖f(iy)‖ ≤ 1`, `‖f z‖ ≤ m` on `|Re z| ≤ 1/4` (with `1 ≤ m`, `1 ≤ ℓ`, `log m ≤ 2ℓ`), and
`f 0 = p ≥ 0`, and suppose `‖f(iu) - p‖ ≤ 2√p E + E²` with `E = 2 |sinh π u| R`.  Then
for real `|t| ≤ 1/(16ℓ)`,
`‖f t‖ - Re f t ≤ t² (8π² R² + 24576 e^{π²} ℓ² √(min 1 R))`.  Area-law manuscript,
proof of Lemma 5.3, `04-conditional.tex`, lines 562–600. -/
theorem norm_sub_re_le_of_phase_bounds {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {m ℓ R p : ℝ} (hm : 1 ≤ m) (hℓ : 1 ≤ ℓ) (hlog : Real.log m ≤ 2 * ℓ) (hR : 0 ≤ R)
    (hp : 0 ≤ p) (hf0 : f 0 = p) (hsymm : ∀ z, f (-(conj z)) = conj (f z))
    (him : ∀ y : ℝ, ‖f (y * I)‖ ≤ 1) (hstrip : ∀ z : ℂ, |z.re| ≤ 1 / 4 → ‖f z‖ ≤ m)
    (hphase : ∀ u : ℝ, ‖f (u * I) - f 0‖ ≤
      4 * √p * |Real.sinh (Real.pi * u)| * R + 4 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2)
    {t : ℝ} (ht : |t| ≤ 1 / (16 * ℓ)) :
    ‖f t‖ - (f t).re ≤
      t ^ 2 * (8 * Real.pi ^ 2 * R ^ 2 + 24576 * Real.exp (Real.pi ^ 2) * ℓ ^ 2 * √(min 1 R)) := by
  have hℓ0 : 0 < ℓ := by linarith
  set b : ℝ := 1 / (8 * ℓ) with hb
  have hb0 : 0 < b := by positivity
  have hb8 : b ≤ 1 / 8 := by rw [hb, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set m' := min 1 R
  have hm'0 : 0 ≤ m' := le_min zero_le_one hR
  have hm'1 : m' ≤ 1 := min_le_left _ _
  have hp1 : p ≤ 1 := by
    have := him 0
    simpa [hf0, abs_of_nonneg hp] using this
  -- the narrow strip bound
  have hnarrow : ∀ z : ℂ, |z.re| ≤ b → ‖f z‖ ≤ Real.exp 1 := fun z hz => by
    simpa using norm_le_exp_one_mul_of_strip hf zero_le_one hm hℓ hlog him
      (fun w hw => by simpa using hstrip w hw) hz
  -- the Gaussian-damped function
  set F : ℂ → ℂ := fun z => (f z - p) * Complex.exp (z ^ 2)
  have hF : Differentiable ℂ F :=
    (hf.sub (differentiable_const _)).mul (differentiable_exp.comp (differentiable_id.pow 2))
  set K1 : ℝ := 8 * Real.exp (Real.pi ^ 2)
  have hK1 : 2 ≤ K1 := by
    have : 1 ≤ Real.exp (Real.pi ^ 2) := Real.one_le_exp (sq_nonneg _)
    simp only [K1]; linarith
  have hnormexp : ∀ z : ℂ, ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    intro z; rw [Complex.norm_exp]; congr 1; simp [sq]
  -- the imaginary axis
  have hFim : ∀ u : ℝ, ‖F (u * I)‖ ≤ K1 * m' := by
    intro u
    have hnorm : ‖F (u * I)‖ = ‖f (u * I) - p‖ * Real.exp (-u ^ 2) := by
      simp only [F, norm_mul, hnormexp]; congr 2; simp
    rw [hnorm]
    rcases le_total R 1 with hR1 | hR1
    · have hm' : m' = R := min_eq_right hR1
      rw [hm']
      have h1 := hphase u
      rw [hf0] at h1
      have hsp : √p ≤ 1 := Real.sqrt_le_one.mpr hp1
      calc ‖f (u * I) - p‖ * Real.exp (-u ^ 2)
          ≤ (4 * |Real.sinh (Real.pi * u)| * R + 4 * Real.sinh (Real.pi * u) ^ 2 * R ^ 2) *
              Real.exp (-u ^ 2) := by
            refine mul_le_mul_of_nonneg_right (h1.trans ?_) (Real.exp_pos _).le
            have : 4 * √p * |Real.sinh (Real.pi * u)| * R ≤ 4 * 1 * |Real.sinh (Real.pi * u)| * R := by
              gcongr
            linarith
        _ ≤ K1 * R := phaseError_mul_exp_le hR hR1 u
    · have hm' : m' = 1 := min_eq_left hR1
      rw [hm', mul_one]
      have h2 : ‖f (u * I) - p‖ ≤ 2 := by
        calc ‖f (u * I) - p‖ ≤ ‖f (u * I)‖ + ‖(p : ℂ)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
            gcongr
            · exact him u
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]; exact hp1
          _ = 2 := by norm_num
      calc ‖f (u * I) - p‖ * Real.exp (-u ^ 2) ≤ 2 * 1 := by
            gcongr
            exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
        _ ≤ K1 := by linarith
  -- the line `Re z = b` and the strip bound
  have hFstrip : ∀ z : ℂ, |z.re| ≤ b → ‖F z‖ ≤ K1 := by
    intro z hz
    have h1 := hnarrow z hz
    have hz2 : z.re ^ 2 - z.im ^ 2 ≤ 1 / 64 := by
      have : z.re ^ 2 ≤ b ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
      have : b ^ 2 ≤ 1 / 64 := by nlinarith
      nlinarith [sq_nonneg z.im]
    have hexp : Real.exp (z.re ^ 2 - z.im ^ 2) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (hz2.trans (by norm_num))
    have hE1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hE2 : Real.exp 1 * Real.exp 1 ≤ Real.exp (Real.pi ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      nlinarith [Real.two_le_pi]
    calc ‖F z‖ = ‖f z - p‖ * Real.exp (z.re ^ 2 - z.im ^ 2) := by
          simp only [F, norm_mul, hnormexp]
      _ ≤ (Real.exp 1 + 1) * Real.exp 1 := by
          gcongr
          calc ‖f z - p‖ ≤ ‖f z‖ + ‖(p : ℂ)‖ := norm_sub_le _ _
            _ ≤ Real.exp 1 + 1 := by
              gcongr
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]; exact hp1
      _ ≤ K1 := by simp only [K1]; nlinarith
  sorry

end Complex

end
