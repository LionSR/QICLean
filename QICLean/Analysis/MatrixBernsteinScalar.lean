import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Real

open Nat

/-- The Bernstein factor. -/
noncomputable def bernsteinFactor (R θ : ℝ) : ℝ :=
  (Real.exp (θ * R) - θ * R - 1) / R ^ 2

private lemma hasSum_exp_sub_one_sub (u : ℝ) :
    HasSum (fun n : ℕ ↦ u ^ (n + 2) / (n + 2)!) (Real.exp u - u - 1) := by
  have h := NormedSpace.expSeries_div_hasSum_exp u
  rw [← congrFun Real.exp_eq_exp_ℝ u] at h
  have := (hasSum_nat_add_iff' 2).mpr h
  convert this using 1
  simp [Finset.sum_range_succ]
  ring

lemma exp_le_one_add_add_sq_div_two_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  let h : ℝ → ℝ := fun x ↦ 1 + x + x ^ 2 / 2 - Real.exp x
  have hd : ∀ x, HasDerivAt h (1 + x - Real.exp x) x := by
    intro x
    have := ((((hasDerivAt_id x).const_add 1).add ((hasDerivAt_pow 2 x).div_const 2))).sub
      (Real.hasDerivAt_exp x)
    convert this using 1
    · ext y; simp [h]
    · norm_num
  have hanti : Antitone h := antitone_of_deriv_nonpos
    (fun x ↦ (hd x).differentiableAt) fun x ↦ by
      rw [(hd x).deriv]; linarith [Real.add_one_le_exp x]
  have := hanti hu
  simp [h] at this
  linarith

lemma factorial_add_two_ge (n : ℕ) : 2 * 3 ^ n ≤ (n + 2)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith


lemma sq_div_two_le_exp_sub_sub_one {v : ℝ} (hv : 0 ≤ v) : v ^ 2 / 2 ≤ Real.exp v - v - 1 := by
  linarith [Real.quadratic_le_exp_of_nonneg hv]

lemma bernsteinFactor_nonneg (R θ : ℝ) : 0 ≤ bernsteinFactor R θ := by
  unfold bernsteinFactor
  have := Real.add_one_le_exp (θ * R)
  exact div_nonneg (by linarith) (sq_nonneg R)

lemma sq_div_two_le_bernsteinFactor {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) :
    θ ^ 2 / 2 ≤ bernsteinFactor R θ := by
  unfold bernsteinFactor
  rw [le_div_iff₀ (by positivity)]
  have := sq_div_two_le_exp_sub_sub_one (mul_nonneg hθ hR.le)
  nlinarith

theorem exp_mul_le_one_add_add_bernsteinFactor_mul_sq {R θ x : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ)
    (hx : x ≤ R) : Real.exp (θ * x) ≤ 1 + θ * x + bernsteinFactor R θ * x ^ 2 := by
  rcases lt_or_ge x 0 with hneg | hpos
  · have h1 := exp_le_one_add_add_sq_div_two_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hθ hneg.le)
    have h2 := sq_div_two_le_bernsteinFactor hR hθ
    nlinarith [sq_nonneg x]
  · set s := x / R with hs
    have hs0 : 0 ≤ s := div_nonneg hpos hR.le
    have hs1 : s ≤ 1 := (div_le_one hR).mpr hx
    have hxs : x = s * R := by rw [hs]; field_simp
    have hle : ∀ n : ℕ, (θ * x) ^ (n + 2) / (n + 2)! ≤
        s ^ 2 * ((θ * R) ^ (n + 2) / (n + 2)!) := by
      intro n
      rw [hxs, show θ * (s * R) = s * (θ * R) by ring, mul_pow, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) (by positivity)
      · exact pow_le_pow_of_le_one hs0 hs1 (by omega)
      · exact pow_nonneg (mul_nonneg hθ hR.le) _
    have key := hasSum_le hle (hasSum_exp_sub_one_sub (θ * x))
      ((hasSum_exp_sub_one_sub (θ * R)).mul_left (s ^ 2))
    have hg : bernsteinFactor R θ * x ^ 2 = s ^ 2 * (Real.exp (θ * R) - θ * R - 1) := by
      unfold bernsteinFactor
      rw [hxs]; field_simp
    linarith

theorem bernsteinFactor_le {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (hθR : θ * R < 3) :
    bernsteinFactor R θ ≤ θ ^ 2 / 2 / (1 - θ * R / 3) := by
  set v := θ * R with hv
  have hv0 : 0 ≤ v := mul_nonneg hθ hR.le
  have hr0 : 0 ≤ v / 3 := by positivity
  have hr1 : v / 3 < 1 := by linarith
  have hle : ∀ n : ℕ, v ^ (n + 2) / (n + 2)! ≤ v ^ 2 / 2 * (v / 3) ^ n := by
    intro n
    have hf : (2 * 3 ^ n : ℝ) ≤ (n + 2)! := by exact_mod_cast factorial_add_two_ge n
    rw [div_le_iff₀ (by positivity), div_pow, pow_add]
    calc v ^ n * v ^ 2 = v ^ 2 / 2 * (v ^ n / 3 ^ n) * (2 * 3 ^ n) := by field_simp
      _ ≤ v ^ 2 / 2 * (v ^ n / 3 ^ n) * (n + 2)! := by gcongr
  have key := hasSum_le hle (hasSum_exp_sub_one_sub v)
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (v ^ 2 / 2))
  have h3 : 0 < 1 - v / 3 := by linarith
  unfold bernsteinFactor
  rw [div_le_iff₀ (by positivity)]
  calc Real.exp v - v - 1 ≤ v ^ 2 / 2 * (1 - v / 3)⁻¹ := key
    _ = θ ^ 2 / 2 / (1 - v / 3) * R ^ 2 := by rw [hv]; field_simp

theorem neg_mul_add_bernsteinFactor_mul_le {R σsq t : ℝ} (hR : 0 < R) (hσ : 0 ≤ σsq)
    (ht : 0 ≤ t) :
    -(t / (σsq + R * t / 3) * t) + bernsteinFactor R (t / (σsq + R * t / 3)) * σsq ≤
      -(t ^ 2 / 2 / (σsq + R * t / 3)) := by
  rcases ht.eq_or_lt with rfl | htpos
  · simp [bernsteinFactor]
  set D := σsq + R * t / 3 with hD
  have hDpos : 0 < D := by positivity
  set θ := t / D with hθ
  have hθ0 : 0 ≤ θ := by positivity
  rcases hσ.eq_or_lt with hσ0 | hσpos
  · subst hσ0
    simp only [mul_zero, add_zero]
    rw [hθ, hD]
    rw [neg_le_neg_iff, zero_add]
    field_simp
    nlinarith
  · have hθR : θ * R < 3 := by
      rw [hθ, div_mul_eq_mul_div, div_lt_iff₀ hDpos]; nlinarith
    have hg := bernsteinFactor_le hR hθ0 hθR
    have h1 : 1 - θ * R / 3 = σsq / D := by rw [hθ, hD]; field_simp; ring
    rw [h1] at hg
    have hb : bernsteinFactor R θ * σsq ≤ θ ^ 2 / 2 * D := by
      calc bernsteinFactor R θ * σsq ≤ θ ^ 2 / 2 / (σsq / D) * σsq := by gcongr
        _ = θ ^ 2 / 2 * D := by field_simp
    have : -(θ * t) + θ ^ 2 / 2 * D = -(t ^ 2 / 2 / D) := by rw [hθ]; field_simp; ring
    linarith

end Real
