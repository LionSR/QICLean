/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ResolventDefect
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The integral of the resolvent defect

For a resolvent compression `A, B, V, b₀` (see `QICLean.Analysis.ResolventDefect`),
write `pₖ = |(U_A* a₀)ₖ|²` and `qⱼ = |(U_B* b₀)ⱼ|²`.  Then
`h(v) = ∑ₖ pₖ / (λₖ + v) - ∑ⱼ qⱼ / (μⱼ + v)` and `∑ₖ pₖ = ∑ⱼ qⱼ`.  This gives

* the two tail bounds `h(v) ≤ ⟨a₀, A⁻¹ a₀⟩` and `h(v) ≤ ⟨b₀, B b₀⟩ / v²`;
* the logarithmic resolvent formula
  `∫₀^∞ h(v) dv = ⟨b₀, log B b₀⟩ - ⟨a₀, log A a₀⟩`.

## Main results

* `Matrix.ResolventCompression.defect_le_inv` and
  `Matrix.ResolventCompression.defect_le_div_sq` — the tail bounds.
* `Matrix.ResolventCompression.integral_defect` — the logarithmic resolvent formula.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 380–408.
-/

open MeasureTheory Set Filter Topology
open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem re_dotProduct_spectralFun_ofReal (U : unitary (Matrix n n ℂ)) (f : n → ℝ)
    (x : n → ℂ) :
    (star x ⬝ᵥ (spectralFun U (fun k => (f k : ℂ)) *ᵥ x)).re =
      ∑ k, f k * Complex.normSq ((star (U : Matrix n n ℂ) *ᵥ x) k) := by
  rw [dotProduct_spectralFun_mulVec, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

theorem re_dotProduct_self_eq_sum (U : unitary (Matrix n n ℂ)) (x : n → ℂ) :
    (star x ⬝ᵥ x).re = ∑ k, Complex.normSq ((star (U : Matrix n n ℂ) *ᵥ x) k) := by
  have h := re_dotProduct_spectralFun_ofReal U (fun _ => 1) x
  simp only [Complex.ofReal_one, spectralFun_one, one_mulVec, one_mul] at h
  exact h

/-- The scalar resolvent difference `1 / (λ + v) - 1 / (1 + v)` is integrable on
`(0, ∞)` with integral `-log λ`. -/
theorem integral_inv_add_sub_inv_one_add {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun v : ℝ => (l + v)⁻¹ - (1 + v)⁻¹) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), ((l + v)⁻¹ - (1 + v)⁻¹) = -Real.log l := by
  set F : ℝ → ℝ := fun v => Real.log (l + v) - Real.log (1 + v)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F ((l + x)⁻¹ - (1 + x)⁻¹) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h1 := ((hasDerivAt_id x).const_add l).log (by simp; linarith)
    have h2 := ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
    have h := h1.sub h2
    convert h using 1
    · rfl
    · simp [one_div]
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact (continuousAt_const.add continuousAt_id).log (by simp; linarith)
    · exact (continuousAt_const.add continuousAt_id).log (by simp)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun v : ℝ => (l + v) / (1 + v)) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := l - 1)).div_atTop
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_add 1
      simp only [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with v hv
      simp only [id]
      field_simp
      ring
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with v hv
    simp only [Function.comp, F]
    rw [Real.log_div (by linarith) (by linarith)]
  have hF0 : F 0 = Real.log l := by simp [F]
  have hint : IntegrableOn (fun v : ℝ => (l + v)⁻¹ - (1 + v)⁻¹) (Ioi 0) := by
    rcases le_total l 1 with h | h
    · refine integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun x hx => ?_) hlim
      have hx' : (0 : ℝ) < x := hx
      exact sub_nonneg.2 (inv_anti₀ (by linarith : 0 < l + x) (by linarith : l + x ≤ 1 + x))
    · refine integrableOn_Ioi_deriv_of_nonpos hcont hderiv (fun x hx => ?_) hlim
      have hx' : (0 : ℝ) < x := hx
      exact sub_nonpos.2 (inv_anti₀ (by linarith : 0 < 1 + x) (by linarith : 1 + x ≤ l + x))
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim, hF0, zero_sub]

namespace ResolventCompression

variable (R : ResolventCompression n m)

/-- The eigencoordinate weights `pₖ = |(U_A* a₀)ₖ|²`. -/
def weightA (k : n) : ℝ := Complex.normSq ((star (R.UA : Matrix n n ℂ) *ᵥ R.a0) k)

/-- The eigencoordinate weights `qⱼ = |(U_B* b₀)ⱼ|²`. -/
def weightB (j : m) : ℝ := Complex.normSq ((star (R.UB : Matrix m m ℂ) *ᵥ R.b0) j)

theorem weightA_nonneg (k : n) : 0 ≤ R.weightA k := Complex.normSq_nonneg _

theorem weightB_nonneg (j : m) : 0 ≤ R.weightB j := Complex.normSq_nonneg _

theorem sum_weightA_eq_sum_weightB : ∑ k, R.weightA k = ∑ j, R.weightB j := by
  simp only [weightA, weightB]
  rw [← re_dotProduct_self_eq_sum, ← re_dotProduct_self_eq_sum, a0,
    star_mulVec_dotProduct, mulVec_mulVec, R.isometry, one_mulVec]

theorem defect_eq_sum (v : ℝ) :
    R.defect v = ∑ k, (R.lam k + v)⁻¹ * R.weightA k - ∑ j, (R.mu j + v)⁻¹ * R.weightB j := by
  rw [defect, resA, resB, re_dotProduct_spectralFun_ofReal, re_dotProduct_spectralFun_ofReal]
  rfl

/-- The quadratic form `⟨a₀, A⁻¹ a₀⟩`. -/
def invQuadA : ℝ := ∑ k, (R.lam k)⁻¹ * R.weightA k

/-- The quadratic form `⟨b₀, B b₀⟩`. -/
def quadB : ℝ := ∑ j, R.mu j * R.weightB j

/-- `h(v) ≤ ⟨a₀, A⁻¹ a₀⟩` for `v ≥ 0`.  Area-law manuscript, `04-conditional.tex`,
lines 396–402. -/
theorem defect_le_invQuadA {v : ℝ} (hv : 0 ≤ v) : R.defect v ≤ R.invQuadA := by
  rw [defect_eq_sum, invQuadA]
  have h1 : ∑ k, (R.lam k + v)⁻¹ * R.weightA k ≤ ∑ k, (R.lam k)⁻¹ * R.weightA k :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
      (inv_anti₀ (R.lam_pos k) (by linarith)) (R.weightA_nonneg k)
  have h2 : 0 ≤ ∑ j, (R.mu j + v)⁻¹ * R.weightB j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (inv_nonneg.2 (by linarith [R.mu_pos j]))
      (R.weightB_nonneg j)
  linarith

/-- `h(v) ≤ ⟨b₀, B b₀⟩ / v²` for `v > 0`.  Area-law manuscript, `04-conditional.tex`,
lines 403–407. -/
theorem defect_le_quadB_div_sq {v : ℝ} (hv : 0 < v) : R.defect v ≤ R.quadB / v ^ 2 := by
  rw [defect_eq_sum, quadB, Finset.sum_div]
  have h1 : ∑ k, (R.lam k + v)⁻¹ * R.weightA k ≤ ∑ k, v⁻¹ * R.weightA k :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
      (inv_anti₀ hv (by linarith [R.lam_pos k])) (R.weightA_nonneg k)
  have h2 : ∀ j, (v⁻¹ - R.mu j / v ^ 2) * R.weightB j ≤ (R.mu j + v)⁻¹ * R.weightB j := by
    intro j
    refine mul_le_mul_of_nonneg_right ?_ (R.weightB_nonneg j)
    have hμ := R.mu_pos j
    rw [show v⁻¹ - R.mu j / v ^ 2 = (v - R.mu j) / v ^ 2 by field_simp]
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (R.mu j)]
  have h3 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h2 j
  have hsum := R.sum_weightA_eq_sum_weightB
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h3
  rw [← Finset.mul_sum] at h1
  have : ∑ j, R.mu j / v ^ 2 * R.weightB j = ∑ j, R.mu j * R.weightB j / v ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [this] at h3
  rw [hsum] at h1
  linarith

/-- The relative logarithmic quadratic form `⟨b₀, log B b₀⟩ - ⟨a₀, log A a₀⟩`. -/
def logGap : ℝ :=
  ∑ j, Real.log (R.mu j) * R.weightB j - ∑ k, Real.log (R.lam k) * R.weightA k

/-- **Logarithmic resolvent formula.** The resolvent defect is integrable on
`(0, ∞)` and `∫₀^∞ h(v) dv = ⟨b₀, log B b₀⟩ - ⟨a₀, log A a₀⟩`.  Area-law manuscript,
`04-conditional.tex`, lines 380–388. -/
theorem integrableOn_defect_and_integral :
    IntegrableOn R.defect (Ioi 0) ∧ ∫ v in Ioi (0 : ℝ), R.defect v = R.logGap := by
  have hsum := R.sum_weightA_eq_sum_weightB
  have hform : ∀ v, R.defect v =
      ∑ k, R.weightA k * ((R.lam k + v)⁻¹ - (1 + v)⁻¹) -
        ∑ j, R.weightB j * ((R.mu j + v)⁻¹ - (1 + v)⁻¹) := by
    intro v
    rw [defect_eq_sum]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
    simp only [mul_comm]
    ring
  have hA := fun k => integral_inv_add_sub_inv_one_add (R.lam_pos k)
  have hB := fun j => integral_inv_add_sub_inv_one_add (R.mu_pos j)
  have hintA : IntegrableOn (fun v => ∑ k, R.weightA k * ((R.lam k + v)⁻¹ - (1 + v)⁻¹))
      (Ioi 0) := integrable_finsetSum _ fun k _ => (hA k).1.const_mul _
  have hintB : IntegrableOn (fun v => ∑ j, R.weightB j * ((R.mu j + v)⁻¹ - (1 + v)⁻¹))
      (Ioi 0) := integrable_finsetSum _ fun j _ => (hB j).1.const_mul _
  have hfun : R.defect = fun v => ∑ k, R.weightA k * ((R.lam k + v)⁻¹ - (1 + v)⁻¹) -
      ∑ j, R.weightB j * ((R.mu j + v)⁻¹ - (1 + v)⁻¹) := funext hform
  refine ⟨hfun ▸ hintA.sub hintB, ?_⟩
  rw [hfun, integral_sub hintA hintB, integral_finsetSum _ fun k _ => (hA k).1.const_mul _,
    integral_finsetSum _ fun j _ => (hB j).1.const_mul _, logGap]
  simp only [integral_const_mul, (hA _).2, (hB _).2]
  simp only [mul_neg, Finset.sum_neg_distrib, mul_comm]
  ring

end ResolventCompression

end Matrix

end
