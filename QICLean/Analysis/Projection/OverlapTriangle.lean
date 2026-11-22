/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Overlaps of unit vectors close to a common vector

If two unit vectors `v` and `v'` both have large overlap with a third unit vector `w`, they
have large overlap with each other. Writing `v = ⟨w, v⟩ w + u` and `v' = ⟨w, v'⟩ w + u'`
with `u, u'` orthogonal to `w`, one has `⟨v, v'⟩ = conj ⟨w, v⟩ ⟨w, v'⟩ + ⟨u, u'⟩` and
`‖u‖² = 1 - |⟨w, v⟩|²`, which gives the bound of the first result below.

## Main results

* `norm_inner_ge_mul_sub_sqrt`: for unit vectors `v, v', w`,
  `|⟨v, v'⟩| ≥ |⟨v, w⟩| |⟨v', w⟩| - √((1 - |⟨v, w⟩|²)(1 - |⟨v', w⟩|²))`.
* `one_sub_two_mul_add_le_norm_inner`: if `|⟨v, w⟩| ≥ 1 - δ` and `|⟨v', w⟩| ≥ 1 - δ'` with
  `0 ≤ δ, δ' ≤ 1`, then `|⟨v, v'⟩| ≥ 1 - 2(δ + δ')`.

The statement is the source's. Its printed proof writes `Γ` for the common vector `w`, and
its second line is an inequality rather than an equality; neither affects the statement.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, Lemma `claim:overlap`,
  lines 307–317.
-/

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Overlap through a common vector.** For unit vectors `v`, `v'` and `w`,
`|⟨v, v'⟩| ≥ |⟨v, w⟩| |⟨v', w⟩| - √((1 - |⟨v, w⟩|²)(1 - |⟨v', w⟩|²))`. This is the first
inequality of the proof of Lemma `claim:overlap` of arXiv:1307.5143v1, `algo53.tex`,
lines 313–316, with `w` in place of the printed `Γ`. -/
theorem norm_inner_ge_mul_sub_sqrt {v v' w : E} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hw : ‖w‖ = 1) :
    ‖⟪v, w⟫_𝕜‖ * ‖⟪v', w⟫_𝕜‖ -
        √((1 - ‖⟪v, w⟫_𝕜‖ ^ 2) * (1 - ‖⟪v', w⟫_𝕜‖ ^ 2)) ≤ ‖⟪v, v'⟫_𝕜‖ := by
  set α := ⟪w, v⟫_𝕜
  set β := ⟪w, v'⟫_𝕜
  set u := v - α • w
  set u' := v' - β • w
  have hww : ⟪w, w⟫_𝕜 = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hwu : ⟪w, u⟫_𝕜 = 0 := by
    simp only [u, inner_sub_right, inner_smul_right, hww, mul_one, α, sub_self]
  have hwu' : ⟪w, u'⟫_𝕜 = 0 := by
    simp only [u', inner_sub_right, inner_smul_right, hww, mul_one, β, sub_self]
  have hu_w : ⟪u, w⟫_𝕜 = 0 := by rw [← inner_conj_symm, hwu, map_zero]
  -- Pythagoras along `w`.
  have hnorm (x y : E) (c : 𝕜) (hc : c = ⟪w, x⟫_𝕜) (hy : y = x - c • w)
      (hwy : ⟪w, y⟫_𝕜 = 0) (hx : ‖x‖ = 1) : ‖y‖ ^ 2 = 1 - ‖c‖ ^ 2 := by
    have hxy : x = c • w + y := by rw [hy]; abel
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • w) y
      (by rw [inner_smul_left, hwy, mul_zero])
    rw [← hxy, hx, norm_smul, hw, mul_one] at h
    linarith
  have hu : ‖u‖ ^ 2 = 1 - ‖α‖ ^ 2 := hnorm v u α rfl rfl hwu hv
  have hu' : ‖u'‖ ^ 2 = 1 - ‖β‖ ^ 2 := hnorm v' u' β rfl rfl hwu' hv'
  -- The inner product splits into the parts along `w` and orthogonal to `w`.
  have hsplit : ⟪v, v'⟫_𝕜 = (starRingEnd 𝕜) α * β + ⟪u, u'⟫_𝕜 := by
    have hv1 : v = α • w + u := by simp only [u]; abel
    have hv2 : v' = β • w + u' := by simp only [u']; abel
    conv_lhs => rw [hv1, hv2]
    rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_left,
      inner_smul_right, inner_smul_right, hww, hwu', hu_w]
    ring
  have hα : ‖⟪v, w⟫_𝕜‖ = ‖α‖ := norm_inner_symm v w
  have hβ : ‖⟪v', w⟫_𝕜‖ = ‖β‖ := norm_inner_symm v' w
  have hsqrt : √((1 - ‖α‖ ^ 2) * (1 - ‖β‖ ^ 2)) = ‖u‖ * ‖u'‖ := by
    rw [← hu, ← hu', ← mul_pow, Real.sqrt_sq (by positivity)]
  rw [hα, hβ, hsqrt, hsplit]
  calc ‖α‖ * ‖β‖ - ‖u‖ * ‖u'‖ ≤ ‖(starRingEnd 𝕜) α * β‖ - ‖⟪u, u'⟫_𝕜‖ := by
        rw [norm_mul, RCLike.norm_conj]
        linarith [norm_inner_le_norm (𝕜 := 𝕜) u u']
    _ ≤ ‖(starRingEnd 𝕜) α * β + ⟪u, u'⟫_𝕜‖ := norm_sub_le_norm_add _ _

/-- **Lemma `claim:overlap`** of Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, lines 307–317. Let `v`, `v'` and `w` be unit vectors and `0 ≤ δ, δ' ≤ 1`. If
`|⟨v, w⟩| ≥ 1 - δ` and `|⟨v', w⟩| ≥ 1 - δ'`, then `|⟨v, v'⟩| ≥ 1 - 2(δ + δ')`. -/
theorem one_sub_two_mul_add_le_norm_inner {v v' w : E} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hw : ‖w‖ = 1) {δ δ' : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδ0' : 0 ≤ δ') (hδ1' : δ' ≤ 1)
    (h : 1 - δ ≤ ‖⟪v, w⟫_𝕜‖) (h' : 1 - δ' ≤ ‖⟪v', w⟫_𝕜‖) :
    1 - 2 * (δ + δ') ≤ ‖⟪v, v'⟫_𝕜‖ := by
  refine le_trans ?_ (norm_inner_ge_mul_sub_sqrt hv hv' hw)
  set a := ‖⟪v, w⟫_𝕜‖
  set b := ‖⟪v', w⟫_𝕜‖
  -- `1 - a² ≤ 2δ` and `1 - b² ≤ 2δ'`, since `a ≥ 1 - δ ≥ 0`.
  have ha : 1 - a ^ 2 ≤ 2 * δ := by nlinarith
  have hb : 1 - b ^ 2 ≤ 2 * δ' := by nlinarith
  have ha1 : a ^ 2 ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := 𝕜) v w
    rw [hv, hw, one_mul] at this
    nlinarith [norm_nonneg ⟪v, w⟫_𝕜]
  have hb1 : b ^ 2 ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := 𝕜) v' w
    rw [hv', hw, one_mul] at this
    nlinarith [norm_nonneg ⟪v', w⟫_𝕜]
  -- `√((1 - a²)(1 - b²)) ≤ 2 √δ √δ' ≤ δ + δ'`.
  have hsq : √((1 - a ^ 2) * (1 - b ^ 2)) ≤ δ + δ' := by
    calc √((1 - a ^ 2) * (1 - b ^ 2)) ≤ √((2 * δ) * (2 * δ')) :=
          Real.sqrt_le_sqrt (mul_le_mul ha hb (by linarith) (by linarith))
      _ = 2 * (√δ * √δ') := by
          rw [show (2 * δ) * (2 * δ') = 2 ^ 2 * (δ * δ') by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num), Real.sqrt_mul hδ0]
      _ ≤ δ + δ' := by
          nlinarith [sq_nonneg (√δ - √δ'), Real.sq_sqrt hδ0, Real.sq_sqrt hδ0']
  -- `a b ≥ (1 - δ)(1 - δ') ≥ 1 - δ - δ'`.
  have hab : 1 - δ - δ' ≤ a * b := by
    nlinarith [mul_le_mul h h' (by linarith) (norm_nonneg _), mul_nonneg hδ0 hδ0']
  linarith
