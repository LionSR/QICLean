/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Product formulas in a Banach algebra

For a family `A : κ → 𝔸` of elements of a complete normed `ℂ`-algebra and an ordering
`order : List κ`, the first-order step `ProductFormula.step A order z = ∏_{k ∈ order} exp(z A_k)`
applies the head of `order` first (it is the rightmost factor). The first-order (Lie) product
formula with `n` steps is `step A order (z / n) ^ n`, and the second-order (Strang) formula
repeats the symmetric step: forward with `z/2`, then backward with `z/2`. Both approximate
`exp(z ∑_k A_k)`.

The estimates are in terms of the commutators of the generators. They take as a hypothesis a
bound `M ≥ 1` on the norms of the exponentials `exp(s z ∑_{k ∈ l} A_k)`, `0 ≤ s ≤ 1`, of the
sums over the sublists `l` of `order`. For skew-adjoint generators in a C*-algebra `M = 1`; in
general `M = exp(‖z‖ ∑_k ‖A_k‖)` (`ProductFormula.norm_exp_smul_gen_le`).

* First order: `‖step A order z - exp(z ∑ A_k)‖ ≤ M^(N+3)/2 ‖z‖² ∑_{i<j} ‖[A_i, A_j]‖`, with `N`
  the length of `order`; after `n` steps the error is divided by `n`.
* Second order: `‖symmStep A order z - exp(z ∑ A_k)‖ ≤ M^(2N+3)/2 ‖z‖³ ∑_{i<j} ‖[A_i, A_j]‖
  ∑_k ‖A_k‖`; after `n` steps it is divided by `n²`.

The one-step estimates for two elements, `norm_exp_mul_exp_sub_exp_add_le` and
`norm_exp_half_mul_exp_mul_exp_half_sub_exp_add_le`, are proved by bounding the derivative of
`s ↦ exp(s x) exp(s y) exp((1 - s)(x + y))`; the steps are then telescoped with
`norm_pow_sub_pow_le`.

## Main definitions

* `ProductFormula.step`, `ProductFormula.lie` — the first-order step and formula.
* `ProductFormula.symmStep`, `ProductFormula.strang` — the second-order step and formula.
* `ProductFormula.gen`, `ProductFormula.commSum`, `ProductFormula.normSum`.
* `ProductFormula.ExpBound` — the bound hypothesis on the exponentials of the partial sums.

## Main results

* `ProductFormula.norm_pow_sub_pow_le` — telescoping.
* `ProductFormula.exp_smul_div_pow` — `exp(z x / n)^n = exp(z x)`.
* `ProductFormula.norm_step_sub_exp_le`, `ProductFormula.norm_lie_sub_exp_le` — first order.
* `ProductFormula.norm_symmStep_sub_exp_le`, `ProductFormula.norm_strang_sub_exp_le` — second
  order.
* `norm_exp_le_real_exp_norm` — `‖exp x‖ ≤ exp ‖x‖`.
-/

open NormedSpace Set

/-- The norm of an exponential is bounded by the scalar exponential of the norm. -/
theorem norm_exp_le_real_exp_norm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hsumx : HasSum (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • x ^ n) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  rw [← hsumx.tsum_eq]
  have hsum : Summable (fun n : ℕ => ‖((Nat.factorial n : ℂ)⁻¹) • x ^ n‖) := by
    simpa using (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x)
  calc
    ‖∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • x ^ n‖
        ≤ ∑' n : ℕ, ‖((Nat.factorial n : ℂ)⁻¹) • x ^ n‖ :=
          norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖x‖ ^ n / Nat.factorial n := by
          exact Summable.tsum_le_tsum (fun n => by
            calc
              ‖((Nat.factorial n : ℂ)⁻¹) • x ^ n‖
                  = ‖((Nat.factorial n : ℂ)⁻¹)‖ * ‖x ^ n‖ := norm_smul _ _
              _ ≤ ‖((Nat.factorial n : ℂ)⁻¹)‖ * ‖x‖ ^ n := by
                    gcongr
                    exact norm_pow_le _ _
              _ = ‖x‖ ^ n / Nat.factorial n := by
                    simp [div_eq_mul_inv, mul_comm])
            hsum (Real.summable_pow_div_factorial ‖x‖)
    _ = Real.exp ‖x‖ := by
          simpa [Real.exp_eq_exp_ℝ] using
            (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) ‖x‖).symm

namespace ProductFormula

/-! ### Telescoping -/

/-- **Telescoping.** If `‖a‖, ‖b‖ ≤ M`, then `‖a^m - b^m‖ ≤ m M^(m-1) ‖a - b‖`. -/
theorem norm_pow_sub_pow_le {R : Type*} [NormedRing R] {a b : R} {M : ℝ} (ha : ‖a‖ ≤ M)
    (hb : ‖b‖ ≤ M) : ∀ m : ℕ, ‖a ^ m - b ^ m‖ ≤ m * M ^ (m - 1) * ‖a - b‖
  | 0 => by simp
  | m + 1 => by
    have hM : 0 ≤ M := (norm_nonneg a).trans ha
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : a ^ (m + 2) - b ^ (m + 2) =
          a ^ (m + 1) * (a - b) + (a ^ (m + 1) - b ^ (m + 1)) * b := by
        rw [pow_succ a (m + 1), pow_succ b (m + 1), mul_sub, sub_mul]
        abel
      have hpow : ‖a ^ (m + 1)‖ ≤ M ^ (m + 1) :=
        (norm_pow_le' a (Nat.succ_pos m)).trans (pow_le_pow_left₀ (norm_nonneg a) ha _)
      rw [hsplit]
      calc ‖a ^ (m + 1) * (a - b) + (a ^ (m + 1) - b ^ (m + 1)) * b‖
          ≤ ‖a ^ (m + 1)‖ * ‖a - b‖ + ‖a ^ (m + 1) - b ^ (m + 1)‖ * ‖b‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ M ^ (m + 1) * ‖a - b‖ + ((m + 1 : ℕ) * M ^ m * ‖a - b‖) * M := by
            gcongr
            simpa using ih
        _ = ((m + 2 : ℕ) : ℝ) * M ^ (m + 2 - 1) * ‖a - b‖ := by
            rw [show m + 2 - 1 = m + 1 by omega]
            push_cast
            ring

section TwoElements

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-! ### Derivatives of exponentials along a real parameter -/

private theorem hasDerivAt_exp_smul (x : 𝔸) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ exp (u • x)) (exp (t • x) * x) t :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) x t

private theorem hasDerivAt_exp_smul' (x : 𝔸) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ exp (u • x)) (x * exp (t • x)) t :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) x t

private theorem hasDerivAt_exp_sub_smul (x : 𝔸) (c t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ exp ((c - u) • x)) (-(exp ((c - t) • x) * x)) t := by
  simpa only [Function.comp_def, neg_smul, one_smul] using
    (hasDerivAt_exp_smul x (c - t)).scomp t ((hasDerivAt_id' t).const_sub c)

private theorem hasDerivAt_exp_sub_smul' (x : 𝔸) (c t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ exp ((c - u) • x)) (-(x * exp ((c - t) • x))) t := by
  simpa only [Function.comp_def, neg_smul, one_smul] using
    (hasDerivAt_exp_smul' x (c - t)).scomp t ((hasDerivAt_id' t).const_sub c)

/-- `exp(z x / n)^n = exp(z x)` for `n ≠ 0`. -/
theorem exp_smul_div_pow {n : ℕ} (hn : n ≠ 0) (z : ℂ) (x : 𝔸) :
    exp ((z / n) • x) ^ n = exp (z • x) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℂ 𝔸
  rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_div_cancel₀ z (Nat.cast_ne_zero.mpr hn)]

/-! ### Two elements -/

/-- `‖exp(s x) - 1‖ ≤ M ‖x‖ s` while `‖exp(u x)‖ ≤ M` for `0 ≤ u ≤ 1`. -/
theorem norm_exp_smul_sub_one_le {x : 𝔸} {M : ℝ}
    (hx : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • x)‖ ≤ M) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖exp (s • x) - 1‖ ≤ M * ‖x‖ * s := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ ↦ exp (u • x))
    (f' := fun u ↦ exp (u • x) * x) (a := 0) (b := s) (C := M * ‖x‖)
    (fun u _ ↦ (hasDerivAt_exp_smul x u).hasDerivWithinAt)
    (fun u hu ↦ (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (hx u ⟨hu.1, hu.2.le.trans hs.2⟩) (norm_nonneg _))) s ⟨hs.1, le_rfl⟩
  simpa using h

/-- `‖[x, exp(s y)]‖ ≤ M² ‖[x, y]‖ s` while `‖exp(u y)‖ ≤ M` for `0 ≤ u ≤ 1`. -/
theorem norm_mul_exp_sub_exp_mul_le (x : 𝔸) {y : 𝔸} {M : ℝ}
    (hy : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • y)‖ ≤ M) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖x * exp (s • y) - exp (s • y) * x‖ ≤ M ^ 2 * ‖x * y - y * x‖ * s := by
  have hG : ∀ u, HasDerivAt (fun u : ℝ ↦ exp ((s - u) • y) * x * exp (u • y))
      (exp ((s - u) • y) * (x * y - y * x) * exp (u • y)) u := fun u ↦
    (((hasDerivAt_exp_sub_smul y s u).mul_const x).mul (hasDerivAt_exp_smul' y u)).congr_deriv
      (by noncomm_ring)
  have hbound : ∀ u ∈ Ico (0 : ℝ) s,
      ‖exp ((s - u) • y) * (x * y - y * x) * exp (u • y)‖ ≤ M ^ 2 * ‖x * y - y * x‖ := by
    intro u hu
    have h1 : ‖exp ((s - u) • y)‖ ≤ M :=
      hy (s - u) ⟨by linarith [hu.2], by linarith [hu.1, hs.2]⟩
    have h2 : ‖exp (u • y)‖ ≤ M := hy u ⟨hu.1, hu.2.le.trans hs.2⟩
    have hM : 0 ≤ M := (norm_nonneg _).trans h2
    calc ‖exp ((s - u) • y) * (x * y - y * x) * exp (u • y)‖
        ≤ ‖exp ((s - u) • y)‖ * ‖x * y - y * x‖ * ‖exp (u • y)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ M * ‖x * y - y * x‖ * M := by gcongr
      _ = M ^ 2 * ‖x * y - y * x‖ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := s)
    (fun u _ ↦ (hG u).hasDerivWithinAt) hbound s ⟨hs.1, le_rfl⟩
  simpa using h

/-- The commutator of `x` with `exp(s y)` is `s [x, y]` up to `(M² + M) ‖y‖ ‖[x, y]‖ s²`. -/
theorem norm_mul_exp_sub_exp_mul_sub_smul_le (x : 𝔸) {y : 𝔸} {M : ℝ}
    (hy : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • y)‖ ≤ M) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(x * exp (s • y) - exp (s • y) * x) - s • (x * y - y * x)‖ ≤
      (M ^ 2 + M) * ‖y‖ * ‖x * y - y * x‖ * s ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c, c = x * y - y * x := ⟨_, rfl⟩
  rw [← hc]
  have hH : ∀ u, HasDerivAt (fun u : ℝ ↦ exp ((s - u) • y) * x * exp (u • y) - u • c)
      (exp ((s - u) • y) * c * exp (u • y) - c) u := by
    intro u
    refine ((((hasDerivAt_exp_sub_smul y s u).mul_const x).mul
      (hasDerivAt_exp_smul' y u)).sub ((hasDerivAt_id' u).smul_const c)).congr_deriv ?_
    subst hc
    rw [one_smul]
    noncomm_ring
  have hM : 0 ≤ M := (norm_nonneg _).trans (hy 0 ⟨le_rfl, zero_le_one⟩)
  have hbound : ∀ u ∈ Ico (0 : ℝ) s,
      ‖exp ((s - u) • y) * c * exp (u • y) - c‖ ≤ (M ^ 2 + M) * ‖y‖ * ‖c‖ * s := by
    intro u hu
    have hsu : s - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1, hs.2]⟩
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.le.trans hs.2⟩
    have e1 := norm_exp_smul_sub_one_le hy hsu
    have e2 := norm_exp_smul_sub_one_le hy hu'
    have n2 := hy u hu'
    have hsplit : exp ((s - u) • y) * c * exp (u • y) - c =
        (exp ((s - u) • y) - 1) * c * exp (u • y) + c * (exp (u • y) - 1) := by
      noncomm_ring
    have hy0 := norm_nonneg y
    have hc0 := norm_nonneg c
    have hyc : 0 ≤ ‖y‖ * ‖c‖ := mul_nonneg hy0 hc0
    rw [hsplit]
    calc ‖(exp ((s - u) • y) - 1) * c * exp (u • y) + c * (exp (u • y) - 1)‖
        ≤ ‖exp ((s - u) • y) - 1‖ * ‖c‖ * ‖exp (u • y)‖ + ‖c‖ * ‖exp (u • y) - 1‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_mul_le _ _))
      _ ≤ (M * ‖y‖ * (s - u)) * ‖c‖ * M + ‖c‖ * (M * ‖y‖ * u) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right e1 hc0) n2 (norm_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg hM hy0) (by linarith [hu.2])) hc0))
            (mul_le_mul_of_nonneg_left e2 hc0)
      _ ≤ (M ^ 2 + M) * ‖y‖ * ‖c‖ * s := by
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM hM) hyc) hu.1,
            mul_nonneg (mul_nonneg hM hyc) (sub_nonneg.2 hu.2.le)]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := s)
    (fun u _ ↦ (hH u).hasDerivWithinAt) hbound s ⟨hs.1, le_rfl⟩
  simp only [sub_self, zero_smul, exp_zero, one_mul, sub_zero, mul_one, zero_smul] at h
  calc ‖(x * exp (s • y) - exp (s • y) * x) - s • c‖
      = ‖(x * exp (s • y) - s • c) - exp (s • y) * x‖ := by congr 1; abel
    _ ≤ (M ^ 2 + M) * ‖y‖ * ‖c‖ * s * s := h
    _ = (M ^ 2 + M) * ‖y‖ * ‖c‖ * s ^ 2 := by ring

/-- **One first-order step for two elements.**
`‖exp x exp y - exp(x + y)‖ ≤ M⁴/2 ‖[x, y]‖` while the exponentials of `s x`, `s y` and
`s (x + y)`, `0 ≤ s ≤ 1`, have norm at most `M`. -/
theorem norm_exp_mul_exp_sub_exp_add_le {x y : 𝔸} {M : ℝ}
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • x)‖ ≤ M) (hy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • y)‖ ≤ M)
    (hxy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (x + y))‖ ≤ M) :
    ‖exp x * exp y - exp (x + y)‖ ≤ M ^ 4 / 2 * ‖x * y - y * x‖ := by
  have hF : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ exp (s • x) * exp (s • y) * exp ((1 - s) • (x + y)))
      (exp (s • x) * (x * exp (s • y) - exp (s • y) * x) * exp ((1 - s) • (x + y))) s :=
    fun s ↦ (((hasDerivAt_exp_smul x s).mul (hasDerivAt_exp_smul y s)).mul
      (hasDerivAt_exp_sub_smul' (x + y) 1 s)).congr_deriv
        (by simp only [Pi.mul_apply]; noncomm_ring)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hx 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨K, hK⟩ : ∃ K, K = M ^ 4 * ‖x * y - y * x‖ := ⟨_, rfl⟩
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖exp (s • x) * (x * exp (s • y) - exp (s • y) * x) * exp ((1 - s) • (x + y))‖ ≤
        K * s := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have h2 := norm_mul_exp_sub_exp_mul_le x hy hs'
    have h3 := hxy (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hC : 0 ≤ M ^ 2 * ‖x * y - y * x‖ * s := mul_nonneg (by positivity) hs.1
    calc _ ≤ ‖exp (s • x)‖ * ‖x * exp (s • y) - exp (s • y) * x‖ *
          ‖exp ((1 - s) • (x + y))‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ M * (M ^ 2 * ‖x * y - y * x‖ * s) * M :=
          mul_le_mul (mul_le_mul (hx s hs') h2 (norm_nonneg _) hM) h3 (norm_nonneg _)
            (mul_nonneg hM hC)
      _ = K * s := by rw [hK]; ring
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ K * (s ^ 2 / 2)) (K * s) s := fun s ↦
    (((hasDerivAt_pow 2 s).div_const 2).const_mul K).congr_deriv (by norm_num)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s : ℝ ↦ exp (s • x) * exp (s • y) * exp ((1 - s) • (x + y)) - exp (x + y))
    (fun s _ ↦ ((hF s).sub_const _).continuousAt.continuousWithinAt)
    (fun s _ ↦ ((hF s).sub_const _).hasDerivWithinAt) (by simp) hB hbound
    (right_mem_Icc.2 zero_le_one)
  simp only [one_smul, sub_self, zero_smul, exp_zero, mul_one] at h
  rw [hK] at h
  linarith

/-- The symmetric step for two elements, with the half written as `h`. -/
private theorem norm_exp_mul_exp_mul_exp_sub_exp_le {h y : 𝔸} {M : ℝ} (hM1 : 1 ≤ M)
    (hh : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • h)‖ ≤ M) (hy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • y)‖ ≤ M)
    (hhy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (h + h + y))‖ ≤ M) :
    ‖exp h * exp y * exp h - exp (h + h + y)‖ ≤ M ^ 5 * ‖h * y - y * h‖ * (‖h‖ + ‖y‖) := by
  have hM : 0 ≤ M := zero_le_one.trans hM1
  have hF : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ ↦ exp (s • h) * (exp (s • y) * exp (s • h)) * exp ((1 - s) • (h + h + y)))
      (exp (s • h) * ((h * exp (s • y) - exp (s • y) * h) * exp (s • h) +
        exp (s • y) * (y * exp (s • h) - exp (s • h) * y)) * exp ((1 - s) • (h + h + y))) s := by
    intro s
    have key : exp (s • h) * h = h * exp (s • h) := (((Commute.refl h).smul_left s).exp_left).eq
    refine (((hasDerivAt_exp_smul h s).mul ((hasDerivAt_exp_smul y s).mul
      (hasDerivAt_exp_smul h s))).mul (hasDerivAt_exp_sub_smul' (h + h + y) 1 s)).congr_deriv ?_
    simp only [Pi.mul_apply, mul_add, add_mul, mul_sub, sub_mul, mul_neg, mul_assoc]
    rw [← mul_assoc (exp (s • h)) h (exp ((1 - s) • (h + h + y))), key, mul_assoc]
    noncomm_ring
  obtain ⟨c, hc⟩ : ∃ c, c = h * y - y * h := ⟨_, rfl⟩
  have hc' : ‖y * h - h * y‖ = ‖c‖ := by rw [hc, norm_sub_rev]
  have hx0 := norm_nonneg h
  have hy0 := norm_nonneg y
  have hc0 := norm_nonneg c
  have hD : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(h * exp (s • y) - exp (s • y) * h) * exp (s • h) +
        exp (s • y) * (y * exp (s • h) - exp (s • h) * y)‖ ≤
        3 * M ^ 3 * ‖c‖ * (‖h‖ + ‖y‖) * s ^ 2 := by
    intro s hs
    have r1 := norm_mul_exp_sub_exp_mul_sub_smul_le h hy hs
    have r2 := norm_mul_exp_sub_exp_mul_sub_smul_le y hh hs
    rw [← hc] at r1
    rw [hc'] at r2
    have e1 := norm_exp_smul_sub_one_le hh hs
    have e2 := norm_exp_smul_sub_one_le hy hs
    have n1 := hh s hs
    have n2 := hy s hs
    have hsplit : (h * exp (s • y) - exp (s • y) * h) * exp (s • h) +
        exp (s • y) * (y * exp (s • h) - exp (s • h) * y) =
        ((h * exp (s • y) - exp (s • y) * h) - s • c) * exp (s • h) +
          exp (s • y) * ((y * exp (s • h) - exp (s • h) * y) - s • (y * h - h * y)) +
          s • (c * (exp (s • h) - 1)) + s • ((1 - exp (s • y)) * c) := by
      subst hc
      simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub, mul_one, one_mul,
        mul_assoc]
      abel
    have hs0 := hs.1
    have hT1 : ‖((h * exp (s • y) - exp (s • y) * h) - s • c) * exp (s • h)‖ ≤
        (M ^ 2 + M) * ‖y‖ * ‖c‖ * s ^ 2 * M :=
      (norm_mul_le _ _).trans (mul_le_mul r1 n1 (norm_nonneg _) (by positivity))
    have hT2 : ‖exp (s • y) * ((y * exp (s • h) - exp (s • h) * y) - s • (y * h - h * y))‖ ≤
        M * ((M ^ 2 + M) * ‖h‖ * ‖c‖ * s ^ 2) :=
      (norm_mul_le _ _).trans (mul_le_mul n2 r2 (norm_nonneg _) hM)
    have hT3 : ‖s • (c * (exp (s • h) - 1))‖ ≤ s * (‖c‖ * (M * ‖h‖ * s)) := by
      rw [norm_smul, Real.norm_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left e1 hc0)) hs0
    have hT4 : ‖s • ((1 - exp (s • y)) * c)‖ ≤ s * (M * ‖y‖ * s * ‖c‖) := by
      rw [norm_smul, Real.norm_of_nonneg hs0]
      refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ?_ hc0)) hs0
      rw [norm_sub_rev]
      exact e2
    rw [hsplit]
    have hM2 : M ≤ M ^ 3 := by nlinarith
    have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
    have hP : 0 ≤ ‖c‖ * (‖h‖ + ‖y‖) * s ^ 2 := by positivity
    calc _ ≤ (M ^ 2 + M) * ‖y‖ * ‖c‖ * s ^ 2 * M + M * ((M ^ 2 + M) * ‖h‖ * ‖c‖ * s ^ 2) +
          s * (‖c‖ * (M * ‖h‖ * s)) + s * (M * ‖y‖ * s * ‖c‖) :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add hT1 hT2)) hT3)) hT4)
      _ = (M ^ 3 + M ^ 2 + M) * (‖c‖ * (‖h‖ + ‖y‖) * s ^ 2) := by ring
      _ ≤ (3 * M ^ 3) * (‖c‖ * (‖h‖ + ‖y‖) * s ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hP
      _ = 3 * M ^ 3 * ‖c‖ * (‖h‖ + ‖y‖) * s ^ 2 := by ring
  obtain ⟨K, hK⟩ : ∃ K, K = M ^ 5 * ‖c‖ * (‖h‖ + ‖y‖) := ⟨_, rfl⟩
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖exp (s • h) * ((h * exp (s • y) - exp (s • y) * h) * exp (s • h) +
        exp (s • y) * (y * exp (s • h) - exp (s • h) * y)) * exp ((1 - s) • (h + h + y))‖ ≤
        3 * K * s ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have h3 := hhy (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc _ ≤ ‖exp (s • h)‖ * ‖(h * exp (s • y) - exp (s • y) * h) * exp (s • h) +
          exp (s • y) * (y * exp (s • h) - exp (s • h) * y)‖ * ‖exp ((1 - s) • (h + h + y))‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ M * (3 * M ^ 3 * ‖c‖ * (‖h‖ + ‖y‖) * s ^ 2) * M :=
          mul_le_mul (mul_le_mul (hh s hs') (hD s hs') (norm_nonneg _) hM) h3 (norm_nonneg _)
            (by positivity)
      _ = 3 * K * s ^ 2 := by rw [hK]; ring
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ K * s ^ 3) (3 * K * s ^ 2) s := fun s ↦
    ((hasDerivAt_pow 3 s).const_mul K).congr_deriv (by norm_num; ring)
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s : ℝ ↦
      exp (s • h) * (exp (s • y) * exp (s • h)) * exp ((1 - s) • (h + h + y)) - exp (h + h + y))
    (fun s _ ↦ ((hF s).sub_const _).continuousAt.continuousWithinAt)
    (fun s _ ↦ ((hF s).sub_const _).hasDerivWithinAt) (by simp) hB hbound
    (right_mem_Icc.2 zero_le_one)
  simp only [one_smul, sub_self, zero_smul, exp_zero, mul_one, one_pow] at hmain
  rw [hK, hc] at hmain
  simpa only [mul_assoc] using hmain

/-- **One symmetric step for two elements.**
`‖exp(x/2) exp y exp(x/2) - exp(x + y)‖ ≤ M⁵/2 ‖[x, y]‖ (‖x‖ + ‖y‖)` for `M ≥ 1`, while the
exponentials of `s x`, `s y` and `s (x + y)`, `0 ≤ s ≤ 1`, have norm at most `M`. -/
theorem norm_exp_half_mul_exp_mul_exp_half_sub_exp_add_le {x y : 𝔸} {M : ℝ} (hM1 : 1 ≤ M)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • x)‖ ≤ M) (hy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • y)‖ ≤ M)
    (hxy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (x + y))‖ ≤ M) :
    ‖exp ((1 / 2 : ℝ) • x) * exp y * exp ((1 / 2 : ℝ) • x) - exp (x + y)‖ ≤
      M ^ 5 / 2 * ‖x * y - y * x‖ * (‖x‖ + ‖y‖) := by
  have hhh : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by rw [← add_smul]; norm_num
  have hh : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (1 / 2 : ℝ) • x)‖ ≤ M := fun s hs ↦ by
    rw [smul_smul]
    exact hx _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h := norm_exp_mul_exp_mul_exp_sub_exp_le hM1 hh hy (by rwa [hhh])
  rw [hhh] at h
  have hc : (1 / 2 : ℝ) • x * y - y * (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • (x * y - y * x) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  have h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [hc, norm_smul, norm_smul, h2] at h
  refine h.trans ?_
  have hX := norm_nonneg x
  have hY := norm_nonneg y
  have hC := norm_nonneg (x * y - y * x)
  have hM5 : 0 ≤ M ^ 5 := by positivity
  nlinarith [mul_nonneg (mul_nonneg hM5 hC) hX]

end TwoElements

/-! ### Product formulas for a family -/

section Family

variable {𝔸 κ : Type*} [NormedRing 𝔸]

/-- The sum of the generators in `order`. -/
def gen (A : κ → 𝔸) (order : List κ) : 𝔸 :=
  (order.map A).sum

/-- `∑_{i<j} ‖[A_{o_i}, A_{o_j}]‖` over the positions of `order`. -/
noncomputable def commSum (A : κ → 𝔸) : List κ → ℝ
  | [] => 0
  | a :: l => (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum + commSum A l

/-- `∑_{k ∈ order} ‖A_k‖`. -/
noncomputable def normSum (A : κ → 𝔸) (order : List κ) : ℝ :=
  (order.map fun k ↦ ‖A k‖).sum

variable (A : κ → 𝔸)

@[simp] theorem gen_nil : gen A [] = 0 := rfl

theorem gen_cons (a : κ) (l : List κ) : gen A (a :: l) = A a + gen A l := by
  simp [gen]

@[simp] theorem commSum_nil : commSum A [] = 0 := rfl

theorem commSum_cons (a : κ) (l : List κ) :
    commSum A (a :: l) = (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum + commSum A l := rfl

theorem normSum_cons (a : κ) (l : List κ) : normSum A (a :: l) = ‖A a‖ + normSum A l := by
  simp [normSum]

theorem normSum_nonneg (l : List κ) : 0 ≤ normSum A l :=
  List.sum_nonneg fun _ h ↦ by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
    exact norm_nonneg _

theorem commSum_nonneg : ∀ l : List κ, 0 ≤ commSum A l
  | [] => le_rfl
  | a :: l => add_nonneg (List.sum_nonneg fun _ h ↦ by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
      exact norm_nonneg _) (commSum_nonneg l)

/-- Under an enumeration of a finite type, `gen` is the sum over the type. -/
theorem gen_eq_sum [Fintype κ] {order : List κ} (h : order.Perm Finset.univ.toList) :
    gen A order = ∑ k, A k := by
  rw [gen, (h.map A).sum_eq, Finset.sum_map_toList]

/-- The commutator of `A a` with a sum is bounded by the sum of the commutators. -/
theorem norm_gen_comm_le (a : κ) : ∀ l : List κ,
    ‖gen A l * A a - A a * gen A l‖ ≤ (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum
  | [] => by simp
  | b :: l => by
    rw [gen_cons, List.map_cons, List.sum_cons]
    calc ‖(A b + gen A l) * A a - A a * (A b + gen A l)‖
        = ‖(A a * A b - A b * A a) * (-1) + (gen A l * A a - A a * gen A l)‖ := by
          congr 1; noncomm_ring
      _ ≤ ‖A a * A b - A b * A a‖ + ‖gen A l * A a - A a * gen A l‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [mul_neg_one, norm_neg]
      _ ≤ _ := add_le_add le_rfl (norm_gen_comm_le a l)

theorem norm_gen_le : ∀ l : List κ, ‖gen A l‖ ≤ normSum A l
  | [] => by simp [normSum]
  | a :: l => by
    rw [gen_cons, normSum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_gen_le l))

theorem normSum_le_of_sublist {l l' : List κ} (h : l.Sublist l') :
    normSum A l ≤ normSum A l' :=
  (h.map _).sum_le_sum fun _ hx ↦ by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

variable [NormedAlgebra ℂ 𝔸]

/-- One first-order step `∏_{k ∈ order} exp(z A_k)`; the head of `order` is applied first. -/
noncomputable def step (A : κ → 𝔸) (order : List κ) (z : ℂ) : 𝔸 :=
  (order.map fun k ↦ exp (z • A k)).reverse.prod

/-- The first-order (Lie) product formula with `n` steps. -/
noncomputable def lie (A : κ → 𝔸) (order : List κ) (z : ℂ) (n : ℕ) : 𝔸 :=
  step A order (z / n) ^ n

/-- One symmetric step: forward with `z/2`, then backward with `z/2`. -/
noncomputable def symmStep (A : κ → 𝔸) (order : List κ) (z : ℂ) : 𝔸 :=
  step A order.reverse (z / 2) * step A order (z / 2)

/-- The second-order (Strang) product formula with `n` steps. -/
noncomputable def strang (A : κ → 𝔸) (order : List κ) (z : ℂ) (n : ℕ) : 𝔸 :=
  symmStep A order (z / n) ^ n

@[simp] theorem step_nil (z : ℂ) : step A [] z = 1 := rfl

theorem step_cons (a : κ) (l : List κ) (z : ℂ) :
    step A (a :: l) z = step A l z * exp (z • A a) := by
  simp [step, List.reverse_cons, List.prod_append]

theorem step_append_singleton (l : List κ) (a : κ) (z : ℂ) :
    step A (l ++ [a]) z = exp (z • A a) * step A l z := by
  simp [step, List.map_append, List.reverse_append, List.prod_cons]

theorem symmStep_cons (a : κ) (l : List κ) (z : ℂ) :
    symmStep A (a :: l) z =
      exp ((z / 2) • A a) * symmStep A l z * exp ((z / 2) • A a) := by
  simp only [symmStep, List.reverse_cons, step_append_singleton, step_cons, mul_assoc]

theorem gen_smul (c : ℂ) (l : List κ) : gen (fun k ↦ c • A k) l = c • gen A l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [gen_cons, gen_cons, ih, smul_add]

theorem normSum_smul (c : ℂ) (l : List κ) :
    normSum (fun k ↦ c • A k) l = ‖c‖ * normSum A l := by
  induction l with
  | nil => simp [normSum]
  | cons a l ih => rw [normSum_cons, normSum_cons, ih, norm_smul, mul_add]

theorem commSum_smul (c : ℂ) : ∀ l : List κ,
    commSum (fun k ↦ c • A k) l = ‖c‖ ^ 2 * commSum A l
  | [] => by simp
  | a :: l => by
    rw [commSum_cons, commSum_cons, commSum_smul c l, mul_add, ← List.sum_map_mul_left]
    refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun b _ ↦ ?_))
    show ‖(c • A a) * (c • A b) - (c • A b) * (c • A a)‖ = ‖c‖ ^ 2 * ‖A a * A b - A b * A a‖
    rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, norm_smul, norm_mul, sq]

/-- The bound hypothesis of the estimates: `‖exp(s z ∑_{k ∈ l} A_k)‖ ≤ M` for every sublist
`l` of `order` and `0 ≤ s ≤ 1`. -/
def ExpBound (A : κ → 𝔸) (order : List κ) (z : ℂ) (M : ℝ) : Prop :=
  ∀ l : List κ, l.Sublist order → ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (z • gen A l))‖ ≤ M

theorem ExpBound.mono {A : κ → 𝔸} {order order' : List κ} {z : ℂ} {M : ℝ}
    (h : ExpBound A order z M) (h' : order'.Sublist order) : ExpBound A order' z M :=
  fun l hl ↦ h l (hl.trans h')

theorem ExpBound.single {A : κ → 𝔸} {order : List κ} {z : ℂ} {M : ℝ}
    (h : ExpBound A order z M) {a : κ} (ha : a ∈ order) :
    ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (z • A a))‖ ≤ M := by
  intro s hs
  simpa [gen] using h [a] (List.singleton_sublist.mpr ha) s hs

variable [CompleteSpace 𝔸]

/-- In a normed algebra with `‖1‖ = 1`, the exponentials are bounded by
`M = exp(‖z‖ ∑_k ‖A_k‖)`. -/
theorem expBound_exp_normSum [NormOneClass 𝔸] (order : List κ) (z : ℂ) :
    ExpBound A order z (Real.exp (‖z‖ * normSum A order)) := by
  intro l hl s hs
  refine (norm_exp_le_real_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hs.1]
  calc s * (‖z‖ * ‖gen A l‖) ≤ 1 * (‖z‖ * normSum A order) := by
        gcongr
        · exact hs.2
        · exact (norm_gen_le A l).trans (normSum_le_of_sublist A hl)
    _ = ‖z‖ * normSum A order := one_mul _

omit [CompleteSpace 𝔸] in
private theorem norm_step_le {order : List κ} {z : ℂ} {M : ℝ} (hM : ExpBound A order z M)
    (hM1 : 1 ≤ M) (h0 : order ≠ []) : ‖step A order z‖ ≤ M ^ order.length := by
  induction order with
  | nil => exact absurd rfl h0
  | cons a l ih =>
    rw [step_cons, List.length_cons, pow_succ]
    have he : ‖exp (z • A a)‖ ≤ M := by
      simpa using hM.single List.mem_cons_self 1 ⟨zero_le_one, le_rfl⟩
    rcases eq_or_ne l [] with rfl | hl
    · simpa using he
    exact (norm_mul_le _ _).trans (mul_le_mul (ih (hM.mono (List.sublist_cons_self a l)) hl)
      he (norm_nonneg _) (by positivity))

/-- **One first-order step.** `‖step A order z - exp(z ∑ A_k)‖ ≤ M^(N+3)/2 ‖z‖² ∑_{i<j}
‖[A_i, A_j]‖`, with `N` the length of `order`. -/
theorem norm_step_sub_exp_le {order : List κ} {z : ℂ} {M : ℝ} (hM : ExpBound A order z M)
    (hM1 : 1 ≤ M) :
    ‖step A order z - exp (z • gen A order)‖ ≤
      M ^ (order.length + 3) / 2 * ‖z‖ ^ 2 * commSum A order := by
  induction order with
  | nil => simp
  | cons a l ih =>
    have hl := hM.mono (List.sublist_cons_self a l)
    set x := z • A a
    set y := z • gen A l
    have hx := hM.single List.mem_cons_self
    have hy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • y)‖ ≤ M :=
      hM l (List.sublist_cons_self a l)
    have hxy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (y + x))‖ ≤ M := by
      intro s hs
      have := hM (a :: l) (List.Sublist.refl _) s hs
      rwa [gen_cons, smul_add, add_comm] at this
    have htwo := norm_exp_mul_exp_sub_exp_add_le hy hx hxy
    have hcomm : ‖y * x - x * y‖ ≤ ‖z‖ ^ 2 *
        (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum := by
      have : y * x - x * y = (z * z) • (gen A l * A a - A a * gen A l) := by
        simp only [x, y, smul_mul_smul_comm, smul_sub]
      rw [this, norm_smul, norm_mul, ← sq]
      exact mul_le_mul_of_nonneg_left (norm_gen_comm_le A a l) (by positivity)
    have hex : ‖exp x‖ ≤ M := by simpa using hx 1 ⟨zero_le_one, le_rfl⟩
    have hsplit : step A (a :: l) z - exp (z • gen A (a :: l)) =
        (step A l z - exp y) * exp x + (exp y * exp x - exp (y + x)) := by
      rw [step_cons, gen_cons, smul_add, add_comm (z • A a)]
      noncomm_ring
    rw [hsplit]
    have hM0 : 0 ≤ M := zero_le_one.trans hM1
    have hS := commSum_nonneg A l
    have hT : 0 ≤ (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum :=
      List.sum_nonneg fun _ h ↦ by obtain ⟨k, -, rfl⟩ := List.mem_map.mp h; exact norm_nonneg _
    have hpow : M ^ (l.length + 3) ≤ M ^ (l.length + 1 + 3) :=
      pow_le_pow_right₀ hM1 (by omega)
    have hpow4 : M ^ 4 ≤ M ^ (l.length + 1 + 3) := pow_le_pow_right₀ hM1 (by omega)
    calc ‖(step A l z - exp y) * exp x + (exp y * exp x - exp (y + x))‖
        ≤ ‖step A l z - exp y‖ * ‖exp x‖ + ‖exp y * exp x - exp (y + x)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ (M ^ (l.length + 3) / 2 * ‖z‖ ^ 2 * commSum A l) * M +
          M ^ 4 / 2 * (‖z‖ ^ 2 * (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum) := by
          gcongr
          · exact ih hl
          · exact htwo.trans (mul_le_mul_of_nonneg_left hcomm (by positivity))
      _ ≤ M ^ ((a :: l).length + 3) / 2 * ‖z‖ ^ 2 * commSum A (a :: l) := by
          rw [commSum_cons, List.length_cons]
          calc (M ^ (l.length + 3) / 2 * ‖z‖ ^ 2 * commSum A l) * M +
                M ^ 4 / 2 * (‖z‖ ^ 2 * (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum)
              = M ^ (l.length + 1 + 3) / 2 * ‖z‖ ^ 2 * commSum A l +
                M ^ 4 / 2 * ‖z‖ ^ 2 * (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum := by ring
            _ ≤ M ^ (l.length + 1 + 3) / 2 * ‖z‖ ^ 2 * commSum A l +
                M ^ (l.length + 1 + 3) / 2 * ‖z‖ ^ 2 *
                  (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right hpow4 zero_le_two) (by positivity)) hT)
            _ = _ := by ring

/-- **First-order product formula.** After `n ≥ 1` steps,
`‖lie A order z n - exp(z ∑ A_k)‖ ≤ M^(N n + 3)/(2n) ‖z‖² ∑_{i<j} ‖[A_i, A_j]‖`, where `M`
bounds the exponentials at the step `z/n`. -/
theorem norm_lie_sub_exp_le {order : List κ} {z : ℂ} {n : ℕ} (hn : 0 < n) {M : ℝ}
    (hM : ExpBound A order (z / n) M) (hM1 : 1 ≤ M) :
    ‖lie A order z n - exp (z • gen A order)‖ ≤
      M ^ (order.length * n + 3) / (2 * n) * ‖z‖ ^ 2 * commSum A order := by
  by_cases h0 : order = []
  · subst h0
    simp [lie]
  have hexp := (exp_smul_div_pow hn.ne' z (gen A order)).symm
  rw [lie, hexp]
  have hstep := norm_step_le A hM hM1 h0
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hE : ‖exp ((z / n) • gen A order)‖ ≤ M ^ order.length := by
    have h1 : ‖exp ((z / n) • gen A order)‖ ≤ M := by
      simpa using hM order (List.Sublist.refl _) 1 ⟨zero_le_one, le_rfl⟩
    exact h1.trans (le_self_pow₀ hM1 (by simpa using h0))
  have hpow := norm_pow_sub_pow_le hstep hE n
  have hone := norm_step_sub_exp_le A hM hM1
  have hz : ‖z / n‖ = ‖z‖ / n := by rw [norm_div, Complex.norm_natCast]
  rw [hz] at hone
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc ‖step A order (z / n) ^ n - exp ((z / n) • gen A order) ^ n‖
      ≤ n * (M ^ order.length) ^ (n - 1) * ‖step A order (z / n) - exp ((z / n) • gen A order)‖ :=
        hpow
    _ ≤ n * (M ^ order.length) ^ (n - 1) *
        (M ^ (order.length + 3) / 2 * (‖z‖ / n) ^ 2 * commSum A order) := by gcongr
    _ = M ^ (order.length * n + 3) / (2 * n) * ‖z‖ ^ 2 * commSum A order := by
        rw [← pow_mul]
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
        simp only [Nat.add_sub_cancel]
        have : order.length * k + (order.length + 3) = order.length * (k + 1) + 3 := by ring
        rw [show M ^ (order.length * (k + 1) + 3) = M ^ (order.length * k) *
          M ^ (order.length + 3) by rw [← pow_add, this]]
        field_simp

omit [CompleteSpace 𝔸] in
private theorem norm_symmStep_le {order : List κ} {z : ℂ} {M : ℝ} (hM : ExpBound A order z M)
    (hM1 : 1 ≤ M) (h0 : order ≠ []) : ‖symmStep A order z‖ ≤ M ^ (2 * order.length) := by
  induction order with
  | nil => exact absurd rfl h0
  | cons a l ih =>
    rw [symmStep_cons, List.length_cons]
    have he : ‖exp ((z / 2) • A a)‖ ≤ M := by
      have := hM.single List.mem_cons_self (1 / 2) ⟨by norm_num, by norm_num⟩
      rwa [← Complex.coe_smul, smul_smul,
        show ((1 / 2 : ℝ) : ℂ) * z = z / 2 by push_cast; ring] at this
    have hM0 : 0 ≤ M := zero_le_one.trans hM1
    rcases eq_or_ne l [] with rfl | hl
    · simpa [symmStep, pow_two] using
        (norm_mul_le _ _).trans (mul_le_mul he he (norm_nonneg _) hM0)
    calc ‖exp ((z / 2) • A a) * symmStep A l z * exp ((z / 2) • A a)‖
        ≤ M * M ^ (2 * l.length) * M :=
          (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul he
            (ih (hM.mono (List.sublist_cons_self a l)) hl) (norm_nonneg _) hM0)) he
            (norm_nonneg _) (by positivity))
      _ = M ^ (2 * (l.length + 1)) := by ring

/-- **One symmetric step.** `‖symmStep A order z - exp(z ∑ A_k)‖ ≤ M^(2N+3)/2 ‖z‖³
∑_{i<j} ‖[A_i, A_j]‖ ∑_k ‖A_k‖`. -/
theorem norm_symmStep_sub_exp_le {order : List κ} {z : ℂ} {M : ℝ} (hM : ExpBound A order z M)
    (hM1 : 1 ≤ M) :
    ‖symmStep A order z - exp (z • gen A order)‖ ≤
      M ^ (2 * order.length + 3) / 2 * ‖z‖ ^ 3 * commSum A order * normSum A order := by
  induction order with
  | nil => simp [symmStep]
  | cons a l ih =>
    have hl := hM.mono (List.sublist_cons_self a l)
    set x := z • A a
    set y := z • gen A l
    have hx := hM.single List.mem_cons_self
    have hy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • y)‖ ≤ M :=
      hM l (List.sublist_cons_self a l)
    have hxy : ∀ s ∈ Icc (0 : ℝ) 1, ‖exp (s • (x + y))‖ ≤ M := by
      intro s hs
      have := hM (a :: l) (List.Sublist.refl _) s hs
      rwa [gen_cons, smul_add] at this
    have htwo := norm_exp_half_mul_exp_mul_exp_half_sub_exp_add_le hM1 hx hy hxy
    have hhalf : (1 / 2 : ℝ) • x = (z / 2) • A a := by
      simp only [x, smul_smul, ← Complex.coe_smul]
      congr 1; push_cast; ring
    rw [hhalf] at htwo
    have hcomm : ‖x * y - y * x‖ ≤ ‖z‖ ^ 2 *
        (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum := by
      have : x * y - y * x = (z * z) • -(gen A l * A a - A a * gen A l) := by
        simp only [x, y, smul_mul_smul_comm, neg_sub, smul_sub]
      rw [this, norm_smul, norm_neg, norm_mul, ← sq]
      exact mul_le_mul_of_nonneg_left (norm_gen_comm_le A a l) (by positivity)
    have hnorm : ‖x‖ + ‖y‖ ≤ ‖z‖ * normSum A (a :: l) := by
      rw [normSum_cons, mul_add, norm_smul, norm_smul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_gen_le A l) (norm_nonneg _))
    have he : ‖exp ((z / 2) • A a)‖ ≤ M := by
      have := hx (1 / 2) ⟨by norm_num, by norm_num⟩
      rwa [hhalf] at this
    have hsplit : symmStep A (a :: l) z - exp (z • gen A (a :: l)) =
        exp ((z / 2) • A a) * (symmStep A l z - exp y) * exp ((z / 2) • A a) +
          (exp ((z / 2) • A a) * exp y * exp ((z / 2) • A a) - exp (x + y)) := by
      rw [symmStep_cons, gen_cons, smul_add]
      noncomm_ring
    rw [hsplit]
    have hM0 : 0 ≤ M := zero_le_one.trans hM1
    have hS := commSum_nonneg A l
    have hN := normSum_nonneg A (a :: l)
    have hNl : normSum A l ≤ normSum A (a :: l) := by
      rw [normSum_cons]; linarith [norm_nonneg (A a)]
    have hT : 0 ≤ (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum :=
      List.sum_nonneg fun _ h ↦ by obtain ⟨k, -, rfl⟩ := List.mem_map.mp h; exact norm_nonneg _
    have hpow5 : M ^ 5 ≤ M ^ (2 * (l.length + 1) + 3) := pow_le_pow_right₀ hM1 (by omega)
    calc ‖exp ((z / 2) • A a) * (symmStep A l z - exp y) * exp ((z / 2) • A a) +
          (exp ((z / 2) • A a) * exp y * exp ((z / 2) • A a) - exp (x + y))‖
        ≤ M * ‖symmStep A l z - exp y‖ * M +
          ‖exp ((z / 2) • A a) * exp y * exp ((z / 2) • A a) - exp (x + y)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right he (norm_nonneg _))) he (norm_nonneg _) (by positivity))
      _ ≤ M * (M ^ (2 * l.length + 3) / 2 * ‖z‖ ^ 3 * commSum A l * normSum A l) * M +
          M ^ 5 / 2 * (‖z‖ ^ 2 * (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum) *
            (‖z‖ * normSum A (a :: l)) := by
          gcongr
          · exact ih hl
          · exact htwo.trans (by gcongr)
      _ ≤ M ^ (2 * (a :: l).length + 3) / 2 * ‖z‖ ^ 3 * commSum A (a :: l) *
            normSum A (a :: l) := by
          rw [commSum_cons, List.length_cons]
          have e1 : M * M ^ (2 * l.length + 3) * M = M ^ (2 * (l.length + 1) + 3) := by ring
          calc M * (M ^ (2 * l.length + 3) / 2 * ‖z‖ ^ 3 * commSum A l * normSum A l) * M +
                M ^ 5 / 2 * (‖z‖ ^ 2 * (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum) *
                  (‖z‖ * normSum A (a :: l))
              = M ^ (2 * (l.length + 1) + 3) / 2 * ‖z‖ ^ 3 * commSum A l * normSum A l +
                M ^ 5 / 2 * ‖z‖ ^ 3 * (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum *
                  normSum A (a :: l) := by rw [← e1]; ring
            _ ≤ M ^ (2 * (l.length + 1) + 3) / 2 * ‖z‖ ^ 3 * commSum A l * normSum A (a :: l) +
                M ^ (2 * (l.length + 1) + 3) / 2 * ‖z‖ ^ 3 *
                  (l.map fun b ↦ ‖A a * A b - A b * A a‖).sum * normSum A (a :: l) := by
                gcongr
            _ = _ := by ring

/-- **Second-order product formula.** After `n ≥ 1` steps,
`‖strang A order z n - exp(z ∑ A_k)‖ ≤ M^(2Nn+3)/(2n²) ‖z‖³ ∑_{i<j} ‖[A_i, A_j]‖ ∑_k ‖A_k‖`,
where `M` bounds the exponentials at the step `z/n`. -/
theorem norm_strang_sub_exp_le {order : List κ} {z : ℂ} {n : ℕ} (hn : 0 < n) {M : ℝ}
    (hM : ExpBound A order (z / n) M) (hM1 : 1 ≤ M) :
    ‖strang A order z n - exp (z • gen A order)‖ ≤
      M ^ (2 * order.length * n + 3) / (2 * n ^ 2) * ‖z‖ ^ 3 * commSum A order *
        normSum A order := by
  by_cases h0 : order = []
  · subst h0
    simp [strang, symmStep]
  have hexp := (exp_smul_div_pow hn.ne' z (gen A order)).symm
  rw [strang, hexp]
  have hstep := norm_symmStep_le A hM hM1 h0
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hE : ‖exp ((z / n) • gen A order)‖ ≤ M ^ (2 * order.length) := by
    have h1 : ‖exp ((z / n) • gen A order)‖ ≤ M := by
      simpa using hM order (List.Sublist.refl _) 1 ⟨zero_le_one, le_rfl⟩
    exact h1.trans (le_self_pow₀ hM1 (by simpa using h0))
  have hpow := norm_pow_sub_pow_le hstep hE n
  have hone := norm_symmStep_sub_exp_le A hM hM1
  have hz : ‖z / n‖ = ‖z‖ / n := by rw [norm_div, Complex.norm_natCast]
  rw [hz] at hone
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc ‖symmStep A order (z / n) ^ n - exp ((z / n) • gen A order) ^ n‖
      ≤ n * (M ^ (2 * order.length)) ^ (n - 1) *
          ‖symmStep A order (z / n) - exp ((z / n) • gen A order)‖ := hpow
    _ ≤ n * (M ^ (2 * order.length)) ^ (n - 1) *
        (M ^ (2 * order.length + 3) / 2 * (‖z‖ / n) ^ 3 * commSum A order *
          normSum A order) := by gcongr
    _ = M ^ (2 * order.length * n + 3) / (2 * n ^ 2) * ‖z‖ ^ 3 * commSum A order *
          normSum A order := by
        rw [← pow_mul]
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
        simp only [Nat.add_sub_cancel]
        have : 2 * order.length * k + (2 * order.length + 3) = 2 * order.length * (k + 1) + 3 := by
          ring
        rw [show M ^ (2 * order.length * (k + 1) + 3) = M ^ (2 * order.length * k) *
          M ^ (2 * order.length + 3) by rw [← pow_add, this]]
        field_simp

end Family

end ProductFormula
