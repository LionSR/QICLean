/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ProductOverlapBootstrap
import QICLean.Analysis.GlobalGap

/-!
# Phase-aligned normalization of a filtered vector

An operator fixes a unit target and preserves its orthogonal complement,
where it has a squared-norm bound. A vector with nonzero target overlap
therefore has a nonzero filtered image. Its normalization admits a phase
choice with an explicit error bound. Applying this to a bipartite operator
also gives the actual Schmidt-rank bound for that normalized output.

The proof reuses homogeneous perpendicular shrinking, the established
phase-minimized normalization estimate, and operator-to-vector rank growth.
No physical filter, initial product vector, or changing-target sequence is
supplied by these auxiliary statements.

Source: AKLV, arXiv:1301.1162v1, Definition `def:AGSP`, lines 296--314,
and the normalized filtering steps in Lemma `l:5`, lines 1023--1048.
-/

open Matrix Complex
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- The actual normalized filtered image has a phase-aligned error controlled
by its original perpendicular component and nonzero target overlap.
AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1023--1048.
The input need not be normalized, and the real shrinking bound need not be
assumed nonnegative. -/
theorem exists_phase_normalized_filter_output
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (Γ x : EuclideanSpace ℂ n) (hΓ : ‖Γ‖ = 1)
    (hfix : toEuclideanLin K Γ = Γ) (δ : ℝ)
    (hperp : ∀ v : EuclideanSpace ℂ n, ‖v‖ = 1 → ⟪Γ, v⟫_ℂ = 0 →
      ⟪Γ, toEuclideanLin K v⟫_ℂ = 0 ∧ ‖toEuclideanLin K v‖ ^ 2 ≤ δ)
    (hoverlap : ⟪Γ, x⟫_ℂ ≠ 0) :
    toEuclideanLin K x ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
      let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
      ‖ψ‖ = 1 ∧
        ‖ψ - Γ‖ ^ 2 ≤
          2 * δ * ‖x - ⟪Γ, x⟫_ℂ • Γ‖ ^ 2 / ‖⟪Γ, x⟫_ℂ‖ ^ 2 := by
  let a : ℂ := ⟪Γ, x⟫_ℂ
  let v := x - a • Γ
  let w := toEuclideanLin K v
  let y := toEuclideanLin K x
  have hΓΓ : ⟪Γ, Γ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hΓ]
  have hv : ⟪Γ, v⟫_ℂ = 0 := by
    simp only [v, inner_sub_right, inner_smul_right, hΓΓ, mul_one, a, sub_self]
  obtain ⟨hw, hwbound⟩ := perpendicular_shrinking_homogeneous
    (toEuclideanLin K) Γ δ hperp v hv
  change ⟪Γ, w⟫_ℂ = 0 at hw
  change ‖w‖ ^ 2 ≤ δ * ‖v‖ ^ 2 at hwbound
  have hdecomp : x = a • Γ + v := by dsimp only [v]; module
  have hy : y = a • Γ + w := by
    dsimp only [y, w]
    rw [hdecomp, map_add, map_smul, hfix]
  have hyinner : ⟪Γ, y⟫_ℂ = a := by
    rw [hy, inner_add_right, inner_smul_right, hΓΓ, hw, mul_one, add_zero]
  have hy0 : y ≠ 0 := by
    intro hz
    have hh := hyinner
    simp only [hz, inner_zero_right] at hh
    exact hoverlap hh.symm
  have hanorm : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr hoverlap) 2
  have hynorm : ‖y‖ ^ 2 = ‖a‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hy]
    simpa only [norm_smul, hΓ, mul_one, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
        (a • Γ) w (by simp only [inner_smul_left, hw, mul_zero])
  let H : Matrix n n ℂ := 1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))
  have hgap : (H - (0 : ℂ) • 1 - (1 : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef := by
    simp only [H, zero_smul, sub_zero, one_smul, sub_self]
    exact PosSemidef.zero
  have hHy : toEuclideanLin H y = w := by
    simp only [H, map_sub, LinearMap.sub_apply, toLpLin_one, LinearMap.id_apply,
      toEuclideanLin_vecMulVec_star_self_apply, hyinner]
    rw [hy]
    module
  have henergy : (⟪y, toEuclideanLin H y⟫_ℂ).re = ‖w‖ ^ 2 := by
    rw [hHy, hy, inner_add_left, inner_smul_left, hw, mul_zero, zero_add,
      inner_self_eq_norm_sq_to_K]
    exact RCLike.re_ofReal_pow (K := ℂ) ‖w‖ 2
  obtain ⟨θ, _hmin, hθ⟩ :=
    exists_isMinOn_sq_norm_normalize_sub_exp_smul_le_of_posSemidef_gap
      hgap (by norm_num : (0 : ℝ) < 1) hΓ hy0
  rw [henergy, sub_zero, div_one] at hθ
  let c : ℂ := exp ((-θ : ℝ) * I)
  have hc : ‖c‖ = 1 := norm_exp_ofReal_mul_I _
  have hcancel : c * exp (θ * I) = 1 := by
    dsimp only [c]
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, inv_mul_cancel₀ (exp_ne_zero _)]
  have hdiff : c • (‖y‖⁻¹ : ℂ) • y - Γ =
      c • ((‖y‖⁻¹ : ℂ) • y - exp (θ * I) • Γ) := by
    rw [smul_sub, smul_smul c (exp (θ * I)), hcancel, one_smul]
  refine ⟨hy0, c, hc, ?_, ?_⟩
  · rw [norm_smul, hc, one_mul]
    change ‖(‖y‖⁻¹ : ℂ) • y‖ = 1
    simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  · rw [hdiff, norm_smul, hc, one_mul]
    calc
      _ ≤ 2 * (‖w‖ ^ 2 / ‖y‖ ^ 2) := hθ
      _ ≤ 2 * (δ * ‖v‖ ^ 2 / ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hwbound (sq_nonneg _)) (by norm_num)
      _ ≤ 2 * (δ * ‖v‖ ^ 2 / ‖a‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply div_le_div_of_nonneg_left ((sq_nonneg _).trans hwbound) hanorm
        linarith [sq_nonneg ‖w‖]
      _ = _ := by change _ = 2 * δ * ‖v‖ ^ 2 / ‖a‖ ^ 2; ring

/-- Phase alignment and normalization preserve the rank bound of the actual
filtered image. AKLV, arXiv:1301.1162v1, Definition `def:AGSP` and the
normalized filtering steps of Lemma `l:5`, lines 1023--1048. -/
theorem exists_phase_normalized_filter_output_of_operatorSchmidtRank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ) (Γ x : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hfix : toEuclideanLin K Γ = Γ) (δ : ℝ)
    (hperp : ∀ v : EuclideanSpace ℂ (m × n), ‖v‖ = 1 → ⟪Γ, v⟫_ℂ = 0 →
      ⟪Γ, toEuclideanLin K v⟫_ℂ = 0 ∧ ‖toEuclideanLin K v‖ ^ 2 ≤ δ)
    (hoverlap : ⟪Γ, x⟫_ℂ ≠ 0) :
    toEuclideanLin K x ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
      let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
      ‖ψ‖ = 1 ∧
        schmidtRank (WithLp.ofLp ψ) ≤ operatorSchmidtRank K * schmidtRank (WithLp.ofLp x) ∧
        ‖ψ - Γ‖ ^ 2 ≤
          2 * δ * ‖x - ⟪Γ, x⟫_ℂ • Γ‖ ^ 2 / ‖⟪Γ, x⟫_ℂ‖ ^ 2 := by
  obtain ⟨hy0, c, hc, hunit, herror⟩ :=
    exists_phase_normalized_filter_output K Γ x hΓ hfix δ hperp hoverlap
  refine ⟨hy0, c, hc, hunit, ?_, herror⟩
  simp only [WithLp.ofLp_smul]
  rw [schmidtRank_smul_eq_of_ne_zero c (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hc),
    schmidtRank_smul_eq_of_ne_zero _ (by exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hy0))]
  exact schmidtRank_mulVec_le K (WithLp.ofLp x)

end Matrix
