/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Boundary integrals over rectangles with simple poles

For a point `p` strictly inside a closed rectangle, the boundary integral of
`u ↦ (u - p)⁻¹` is `2πi`. Combined with the Cauchy--Goursat theorem for rectangles,
this computes the boundary integral of a function with finitely many simple poles
inside the rectangle: if `f - Σ c_p / (u - p)` extends continuously to the closed
rectangle, the boundary integral of `f` is `2πi Σ c_p`.

The boundary integral is written in the form of Mathlib's Cauchy--Goursat theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: bottom
edge minus top edge plus `I` times (right edge minus left edge).

## Main results

* `Complex.integral_boundary_rect_inv_sub` — the boundary integral of `(u - p)⁻¹`.
* `Complex.integral_boundary_rect_eq_of_simple_poles` — the boundary integral of a
  function with simple poles.
-/

open Set MeasureTheory intervalIntegral Real
open scoped Interval

namespace Complex

/-- The boundary integral of a function over the rectangle with opposite corners `z` and
`w`, in the orientation of Mathlib's Cauchy--Goursat theorem. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

private theorem horizontal_ne_zero {p : ℂ} {y : ℝ} (hy : y ≠ p.im) (x : ℝ) :
    (x : ℂ) + y * I - p ∈ slitPlane := by
  refine Or.inr ?_
  simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    zero_add, add_zero]
  exact sub_ne_zero.mpr hy

/-- A horizontal edge at height `y ≠ Im p`. -/
private theorem integral_horizontal {p : ℂ} {y : ℝ} (hy : y ≠ p.im) (a b : ℝ) :
    ∫ x : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹ =
      log ((b : ℂ) + y * I - p) - log ((a : ℂ) + y * I - p) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ log ((t : ℂ) + y * I - p))
      ((x : ℂ) + y * I - p)⁻¹ x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * I - p) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const (y * I - p) |>.congr_deriv
        (by simp) |> fun h ↦ by simpa [add_sub_assoc] using h
    simpa [one_div] using h1.clog_real (horizontal_ne_zero hy x)
  have hcont : Continuous fun x : ℝ ↦ ((x : ℂ) + y * I - p)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun x ↦ ?_
    exact slitPlane_ne_zero (horizontal_ne_zero hy x)
  exact integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x) (hcont.intervalIntegrable _ _)

private theorem vertical_ne_zero {p : ℂ} {x : ℝ} (hx : x ≠ p.re) (y : ℝ) :
    (x : ℂ) + y * I - p ≠ 0 := by
  intro h
  have := congrArg re h
  simp at this
  exact hx (by linarith)

/-- The right edge, at `x > Re p`. -/
private theorem integral_vertical_right {p : ℂ} {x : ℝ} (hx : p.re < x) (a b : ℝ) :
    ∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹ =
      (log ((x : ℂ) + b * I - p) - log ((x : ℂ) + a * I - p)) / I := by
  have hslit : ∀ y : ℝ, (x : ℂ) + y * I - p ∈ slitPlane := fun y ↦ Or.inl (by simp; linarith)
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ ↦ log ((x : ℂ) + t * I - p) / I)
      ((x : ℂ) + y * I - p)⁻¹ y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * I - p) I y := by
      have := (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
      simpa [add_sub_assoc] using this.sub_const p
    have h2 := (h1.clog_real (hslit y)).div_const I
    refine h2.congr_deriv ?_
    field_simp
  have hcont : Continuous fun y : ℝ ↦ ((x : ℂ) + y * I - p)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun y ↦ vertical_ne_zero hx.ne' y
  exact integral_eq_sub_of_hasDerivAt (fun y _ ↦ hderiv y) (hcont.intervalIntegrable _ _)
    |>.trans (by ring)

/-- The left edge, at `x < Re p`. -/
private theorem integral_vertical_left {p : ℂ} {x : ℝ} (hx : x < p.re) (a b : ℝ) :
    ∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹ =
      (log (-((x : ℂ) + b * I - p)) - log (-((x : ℂ) + a * I - p))) / I := by
  have hslit : ∀ y : ℝ, -((x : ℂ) + y * I - p) ∈ slitPlane := fun y ↦ Or.inl (by simp; linarith)
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ ↦ log (-((x : ℂ) + t * I - p)) / I)
      ((x : ℂ) + y * I - p)⁻¹ y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ ↦ -((x : ℂ) + t * I - p)) (-I) y := by
      have := ((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)).sub_const p
      convert this.neg using 1
      · ext t; simp
      · simp
    have h2 := (h1.clog_real (hslit y)).div_const I
    refine h2.congr_deriv ?_
    have hne := vertical_ne_zero hx.ne y
    field_simp
  have hcont : Continuous fun y : ℝ ↦ ((x : ℂ) + y * I - p)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun y ↦ vertical_ne_zero hx.ne y
  exact integral_eq_sub_of_hasDerivAt (fun y _ ↦ hderiv y) (hcont.intervalIntegrable _ _)
    |>.trans (by ring)

private theorem log_sub_log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    log u - log (-u) = π * I := by
  rw [log, log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast; ring

private theorem log_sub_log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    log u - log (-u) = -(π * I) := by
  rw [log, log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hu]
  push_cast; ring

/-- **The boundary integral of `(u - p)⁻¹`** over a rectangle containing `p` in its
interior is `2πi`. -/
theorem integral_boundary_rect_inv_sub {z w p : ℂ} (hre : z.re < p.re ∧ p.re < w.re)
    (him : z.im < p.im ∧ p.im < w.im) :
    rectBoundaryIntegral (fun u ↦ (u - p)⁻¹) z w = 2 * π * I := by
  unfold rectBoundaryIntegral
  rw [integral_horizontal him.1.ne, integral_horizontal him.2.ne',
    integral_vertical_right hre.2, integral_vertical_left hre.1]
  have hT : 0 < ((z.re : ℂ) + w.im * I - p).im := by simp; linarith [him.2]
  have hB : ((z.re : ℂ) + z.im * I - p).im < 0 := by simp; linarith [him.1]
  have h1 := log_sub_log_neg_of_im_pos hT
  have h2 := log_sub_log_neg_of_im_neg hB
  simp only [smul_eq_mul, mul_div_cancel₀ _ I_ne_zero]
  linear_combination h1 - h2

/-- The four edges of the closed rectangle with corners `z` and `w`. -/
def rectEdges (z w : ℂ) : Set ℂ :=
  ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ∩ {u | u.re = z.re ∨ u.re = w.re ∨ u.im = z.im ∨ u.im = w.im}

/-- The boundary integral is additive for integrands continuous on the edges. -/
private theorem rectBoundaryIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (rectEdges z w)) (hg : ContinuousOn g (rectEdges z w)) :
    rectBoundaryIntegral (fun u ↦ f u + g u) z w =
      rectBoundaryIntegral f z w + rectBoundaryIntegral g z w := by
  have hh : ∀ {F : ℂ → ℂ}, ContinuousOn F (rectEdges z w) →
      (IntervalIntegrable (fun x : ℝ ↦ F (x + z.im * I)) volume z.re w.re) ∧
      (IntervalIntegrable (fun x : ℝ ↦ F (x + w.im * I)) volume z.re w.re) ∧
      (IntervalIntegrable (fun y : ℝ ↦ F (w.re + y * I)) volume z.im w.im) ∧
      (IntervalIntegrable (fun y : ℝ ↦ F (z.re + y * I)) volume z.im w.im) := by
    intro F hF
    refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
      refine hF.comp (by fun_prop) fun t ht ↦ ?_ <;>
      simp [rectEdges, mem_reProdIm, ht, left_mem_uIcc, right_mem_uIcc]
  obtain ⟨f1, f2, f3, f4⟩ := hh hf
  obtain ⟨g1, g2, g3, g4⟩ := hh hg
  unfold rectBoundaryIntegral
  rw [integral_add f1 g1, integral_add f2 g2, integral_add f3 g3, integral_add f4 g4]
  simp only [smul_add]
  ring

/-- The boundary integral of a finite sum of integrands continuous on the edges. -/
private theorem rectBoundaryIntegral_finset_sum {ι : Type*} (P : Finset ι) {F : ι → ℂ → ℂ}
    {z w : ℂ} (hF : ∀ i ∈ P, ContinuousOn (F i) (rectEdges z w)) :
    rectBoundaryIntegral (fun u ↦ ∑ i ∈ P, F i u) z w = ∑ i ∈ P, rectBoundaryIntegral (F i) z w := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [rectBoundaryIntegral]
  | insert a P ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectBoundaryIntegral_add (hF a (Finset.mem_insert_self a P))
      (continuousOn_finsetSum _ fun i hi ↦ hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hF i (Finset.mem_insert_of_mem hi)]

/-- The boundary integral of a constant multiple. -/
private theorem rectBoundaryIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectBoundaryIntegral (fun u ↦ c * f u) z w = c * rectBoundaryIntegral f z w := by
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- The boundary integral depends only on the values on the boundary. -/
private theorem rectBoundaryIntegral_congr {f g : ℂ → ℂ} {z w : ℂ}
    (h : ∀ u ∈ rectEdges z w, f u = g u) :
    rectBoundaryIntegral f z w = rectBoundaryIntegral g z w := by
  unfold rectBoundaryIntegral
  congr 1; congr 1; congr 1
  · exact integral_congr fun x hx ↦ h _ (by simp [rectEdges, mem_reProdIm, hx, left_mem_uIcc])
  · exact integral_congr fun x hx ↦ h _ (by simp [rectEdges, mem_reProdIm, hx, right_mem_uIcc])
  · congr 1
    exact integral_congr fun y hy ↦ h _ (by simp [rectEdges, mem_reProdIm, hy, right_mem_uIcc])
  · congr 1
    exact integral_congr fun y hy ↦ h _ (by simp [rectEdges, mem_reProdIm, hy, left_mem_uIcc])

/-- **Boundary integrals with simple poles.** Let `P` be a finite set of points strictly
inside the rectangle with corners `z`, `w`. If `f` is complex differentiable on the open
rectangle away from `P`, and `f - Σ_{p ∈ P} c_p (u - p)⁻¹` agrees away from `P` with a
function `g` continuous on the closed rectangle, then the boundary integral of `f` is
`2πi Σ_{p ∈ P} c_p`. -/
theorem integral_boundary_rect_eq_of_simple_poles {f g : ℂ → ℂ} {z w : ℂ} (P : Finset ℂ)
    (c : ℂ → ℂ) (hP : ∀ p ∈ P, (z.re < p.re ∧ p.re < w.re) ∧ (z.im < p.im ∧ p.im < w.im))
    (hg : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ P →
      g u = f u - ∑ p ∈ P, c p * (u - p)⁻¹)
    (hgc : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hfd : ∀ u ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      u ∉ P → DifferentiableAt ℂ f u) :
    rectBoundaryIntegral f z w = 2 * π * I * ∑ p ∈ P, c p := by
  set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  set U := Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)
  have hUR : U ⊆ R := by
    intro u hu
    simp only [U, R, mem_reProdIm, mem_Ioo] at hu ⊢
    exact ⟨⟨hu.1.1.le, hu.1.2.le⟩, ⟨hu.2.1.le, hu.2.2.le⟩⟩
  have hedge : ∀ u ∈ rectEdges z w, u ∉ P := by
    rintro u ⟨-, hb⟩ hu
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hP u hu
    rcases hb with hb | hb | hb | hb <;> linarith
  have hpole : ∀ p ∈ P, ContinuousOn (fun u ↦ c p * (u - p)⁻¹) (rectEdges z w) := by
    intro p hp
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u hu ↦ ?_)
    exact sub_ne_zero.mpr fun h ↦ hedge u hu (h ▸ hp)
  -- The regular part has vanishing boundary integral.
  have hgd : ∀ u ∈ U \ (P : Set ℂ), DifferentiableAt ℂ g u := by
    rintro u ⟨hu, huP⟩
    have hopen : IsOpen (U \ (P : Set ℂ)) :=
      (isOpen_Ioo.reProdIm isOpen_Ioo).sdiff P.finite_toSet.isClosed
    have heq : g =ᶠ[nhds u] fun v ↦ f v - ∑ p ∈ P, c p * (v - p)⁻¹ := by
      filter_upwards [hopen.mem_nhds ⟨hu, huP⟩] with v hv
      exact hg v (hUR hv.1) hv.2
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    refine (hfd u hu huP).sub (DifferentiableAt.fun_sum fun p hp ↦ ?_)
    refine (differentiableAt_const _).mul ((differentiableAt_id.sub_const p).inv ?_)
    exact sub_ne_zero.mpr fun h ↦ huP (by simp only [id] at h; rw [h]; exact hp)
  have h0 := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable g z w P
    P.countable_toSet hgc hgd
  have hgedge : ContinuousOn g (rectEdges z w) := hgc.mono inter_subset_left
  have hcongr : rectBoundaryIntegral f z w =
      rectBoundaryIntegral (fun u ↦ g u + ∑ p ∈ P, c p * (u - p)⁻¹) z w :=
    rectBoundaryIntegral_congr fun u hu ↦ by rw [hg u hu.1 (hedge u hu)]; ring
  rw [hcongr, rectBoundaryIntegral_add hgedge (continuousOn_finsetSum _ hpole),
    rectBoundaryIntegral_finset_sum P hpole]
  have hg0 : rectBoundaryIntegral g z w = 0 := h0
  rw [hg0, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [rectBoundaryIntegral_const_mul, integral_boundary_rect_inv_sub (hP p hp).1 (hP p hp).2]
  ring

end Complex
