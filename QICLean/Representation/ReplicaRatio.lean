/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaWeight

/-!
# Asymptotics of the marked replica ratio

Fix `d ≥ 1` and `0 < t < 1`. The marked ratio of the replica label function on a removable
branch with `k` copies and shifted part `l` is (`05-replicas.tex`, equation
`replicas:ratio-eigenvalue`, lines 403–409)

`r(k, l) = Γ(c + t(k - 1))/Γ(c + t k) · Γ(1 + t l)/Γ(1 + t(l - 1))`.

The area-law paper (*A two-dimensional area law from a global spectral gap*, lines 410–417)
states that gamma ratios give `r ≍ ((l + 1)/k)^t`, and that `r` converges to
`max((l - d)/k, 0)^t` uniformly; `(l - d)/k` is the eigenvalue `(λ_i - i)/k` of the star
operator on the branch. This file proves both assertions for `1 ≤ l ≤ k + d`, the range of
the shifted parts of the labels with at most `d` rows, with the explicit uniform rate
`O(k^(-t))`.

The proof is written from the paper; no Lean source was adapted.

## Main declarations

* `Real.abs_rpow_sub_rpow_le` — `|a^t - b^t| ≤ |a - b|^t` for `a, b ≥ 0`, `0 ≤ t ≤ 1`.
* `Partition.exists_replicaRatio_bounds` — `C⁻¹ (l/k)^t ≤ r(k, l) ≤ C`.
* `Partition.exists_abs_replicaRatio_sub_le` — `|r(k, l) - max((l - d)/k, 0)^t| ≤ C k^(-t)`.
-/

open Real

namespace Real

/-- Hölder continuity of `x ↦ x^t` on `[0, ∞)`: `|a^t - b^t| ≤ |a - b|^t` for
`0 ≤ t ≤ 1`. -/
theorem abs_rpow_sub_rpow_le {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |a ^ t - b ^ t| ≤ |a - b| ^ t := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have h := rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb ht0 ht1
  rw [sub_add_cancel] at h
  have hmono : b ^ t ≤ a ^ t := rpow_le_rpow hb hab ht0
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

end Real

namespace Partition

variable {d : ℕ} {t : ℝ}

/-- The marked ratio as a quotient of two Wendel ratios:
`r(k, l) = (Γ(x + t)/Γ(x)) / (Γ(y + t)/Γ(y))` with `x = 1 + t(l - 1)` and
`y = c + t(k - 1)`. -/
theorem replicaRatio_eq_div (k l : ℝ) :
    replicaRatio d t k l =
      (Gamma (1 + t * (l - 1) + t) / Gamma (1 + t * (l - 1))) /
        (Gamma (replicaConst d t + t * (k - 1) + t) / Gamma (replicaConst d t + t * (k - 1))) := by
  unfold replicaRatio
  have e1 : 1 + t * (l - 1) + t = 1 + t * l := by ring
  have e2 : replicaConst d t + t * (k - 1) + t = replicaConst d t + t * k := by ring
  rw [e1, e2, div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]

/-- Two-sided Wendel bounds for the marked ratio: with `x = 1 + t(l - 1)` and
`y = c + t(k - 1)`, `(1 - t)(x/y)^t ≤ r(k, l) ≤ (x/y)^t / (1 - t)` and
`|r(k, l) - (x/y)^t| ≤ t (1 + (x/y)^t/(1 - t)) / y^t`. -/
theorem replicaRatio_wendel (hd : 0 < d) (ht0 : 0 < t) (ht1 : t < 1) {k l : ℝ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    let x := 1 + t * (l - 1)
    let y := replicaConst d t + t * (k - 1)
    (1 - t) * (x / y) ^ t ≤ replicaRatio d t k l ∧
      replicaRatio d t k l ≤ (x / y) ^ t / (1 - t) ∧
      |replicaRatio d t k l - (x / y) ^ t| ≤ t * (1 + (x / y) ^ t / (1 - t)) / y ^ t := by
  intro x y
  have hc := one_le_replicaConst hd ht0.le
  have hx1 : 1 ≤ x := by simp only [x]; nlinarith
  have hy1 : 1 ≤ y := by simp only [y]; nlinarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxt : 1 ≤ x ^ t := one_le_rpow hx1 ht0.le
  have hyt : 1 ≤ y ^ t := one_le_rpow hy1 ht0.le
  have hxyt : (x / y) ^ t = x ^ t / y ^ t := div_rpow hx0.le hy0.le t
  set N := Gamma (x + t) / Gamma x
  set D := Gamma (y + t) / Gamma y
  have hN1 : N ≤ x ^ t := Gamma_add_div_Gamma_le_rpow hx0 ht0.le ht1.le
  have hN2 : x ^ t - t ≤ N := rpow_sub_le_Gamma_add_div_Gamma hx1 ht0.le ht1.le
  have hD1 : D ≤ y ^ t := Gamma_add_div_Gamma_le_rpow hy0 ht0.le ht1.le
  have hD2 : y ^ t - t ≤ D := rpow_sub_le_Gamma_add_div_Gamma hy1 ht0.le ht1.le
  have hr : replicaRatio d t k l = N / D := replicaRatio_eq_div k l
  have hyt0 : 0 < y ^ t := by linarith
  have hDlo : (1 - t) * y ^ t ≤ D := by nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by nlinarith) hDlo
  have hNlo : (1 - t) * x ^ t ≤ N := by nlinarith
  have hN0 : 0 < N := lt_of_lt_of_le (by nlinarith) hNlo
  rw [hr, hxyt]
  refine ⟨?_, ?_, ?_⟩
  · -- `(1 - t) x^t / y^t ≤ N / y^t ≤ N / D`.
    calc (1 - t) * (x ^ t / y ^ t) = (1 - t) * x ^ t / y ^ t := by ring
      _ ≤ N / y ^ t := div_le_div_of_nonneg_right hNlo hyt0.le
      _ ≤ N / D := div_le_div_of_nonneg_left hN0.le hD0 hD1
  · calc N / D ≤ x ^ t / D := div_le_div_of_nonneg_right hN1 hD0.le
      _ ≤ x ^ t / ((1 - t) * y ^ t) :=
        div_le_div_of_nonneg_left (by linarith) (by nlinarith) hDlo
      _ = x ^ t / y ^ t / (1 - t) := by rw [mul_comm, div_div]
  · rw [abs_le]
    constructor
    · -- `x^t/y^t - N/D ≤ x^t/y^t - N/y^t ≤ t/y^t`.
      have h1 : N / y ^ t ≤ N / D := div_le_div_of_nonneg_left hN0.le hD0 hD1
      have h2 : x ^ t / y ^ t - N / y ^ t ≤ t / y ^ t := by
        rw [← sub_div]; exact div_le_div_of_nonneg_right (by linarith) hyt0.le
      have h3 : t / y ^ t ≤ t * (1 + x ^ t / y ^ t / (1 - t)) / y ^ t := by
        refine div_le_div_of_nonneg_right ?_ hyt0.le
        have : 0 ≤ x ^ t / y ^ t / (1 - t) := by
          have : 0 < 1 - t := by linarith
          positivity
        nlinarith
      linarith
    · -- `N/D - x^t/y^t ≤ x^t/D - x^t/y^t = x^t (y^t - D)/(D y^t) ≤ x^t t/((1-t) y^t y^t)`.
      have h1 : N / D ≤ x ^ t / D := div_le_div_of_nonneg_right hN1 hD0.le
      have h2 : x ^ t / D - x ^ t / y ^ t ≤ t * (x ^ t / y ^ t / (1 - t)) / y ^ t := by
        have h1t : 0 < 1 - t := by linarith
        rw [div_sub_div _ _ hD0.ne' hyt0.ne', div_le_div_iff₀ (mul_pos hD0 hyt0) hyt0]
        have hnum : x ^ t * y ^ t - D * x ^ t ≤ x ^ t * t := by nlinarith
        have : t * (x ^ t / y ^ t / (1 - t)) * (D * y ^ t) =
            x ^ t * t * (D / (1 - t)) := by field_simp
        rw [this]
        have hDy : y ^ t ≤ D / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
        have hxt0 : 0 ≤ x ^ t * t := by positivity
        calc (x ^ t * y ^ t - D * x ^ t) * y ^ t ≤ x ^ t * t * y ^ t :=
              mul_le_mul_of_nonneg_right hnum hyt0.le
          _ ≤ x ^ t * t * (D / (1 - t)) := mul_le_mul_of_nonneg_left hDy hxt0
      have h3 : t * (x ^ t / y ^ t / (1 - t)) / y ^ t ≤
          t * (1 + x ^ t / y ^ t / (1 - t)) / y ^ t :=
        div_le_div_of_nonneg_right (by nlinarith) hyt0.le
      linarith

/-- Elementary comparisons on the admissible range `1 ≤ k`, `1 ≤ l ≤ k + d`:
`t k ≤ y`, `x ≤ (1 + d) y`, `t l ≤ x` and `y ≤ (c + t) k`. -/
private theorem admissible_bounds (hd : 0 < d) (ht0 : 0 < t) (ht1 : t < 1) {k l : ℝ}
    (hk : 1 ≤ k) (hlk : l ≤ k + d) :
    t * k ≤ replicaConst d t + t * (k - 1) ∧
      1 + t * (l - 1) ≤ (1 + d) * (replicaConst d t + t * (k - 1)) ∧
      t * l ≤ 1 + t * (l - 1) ∧
      replicaConst d t + t * (k - 1) ≤ (replicaConst d t + t) * k := by
  have hc := one_le_replicaConst hd ht0.le
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨by nlinarith, ?_, by nlinarith, by nlinarith⟩
  have h1 : (1 + d) * (1 + t * (k - 1)) ≤ (1 + d) * (replicaConst d t + t * (k - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : t * l ≤ t * (k + d) := mul_le_mul_of_nonneg_left hlk ht0.le
  have h3 : 0 ≤ (d : ℝ) * t * (k - 1) := by
    have : 0 ≤ k - 1 := by linarith
    positivity
  have h4 : t * d ≤ d := by nlinarith
  nlinarith

/-- **Lemma 6.2, size of the marked ratio** (`05-replicas.tex`, line 410:
`r_{λ,i} ≍_{d,t} ((l_i + 1)/k)^t`): on the admissible range `1 ≤ k`, `1 ≤ l ≤ k + d`, there is
`C ≥ 1` with `C⁻¹ (l/k)^t ≤ r(k, l) ≤ C`. -/
theorem exists_replicaRatio_bounds (hd : 0 < d) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C, 1 ≤ C ∧ ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k + d →
      C⁻¹ * ((l : ℝ) / k) ^ t ≤ replicaRatio d t k l ∧ replicaRatio d t k l ≤ C := by
  set c := replicaConst d t
  have hc := one_le_replicaConst hd ht0.le
  have h1t : 0 < 1 - t := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set α := (1 - t) * (t / (c + t)) ^ t
  have hα0 : 0 < α := mul_pos h1t (rpow_pos_of_pos (by positivity) _)
  set β := (1 + d) / (1 - t)
  have hβ1 : 1 ≤ β := by rw [le_div_iff₀ h1t]; linarith
  refine ⟨max β α⁻¹, le_max_of_le_left hβ1, fun k l hk hl hlk => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlk' : (l : ℝ) ≤ k + d := by exact_mod_cast hlk
  obtain ⟨hw1, hw2, -⟩ := replicaRatio_wendel hd ht0 ht1 hk' hl'
  obtain ⟨_, hxy, htl, hyk⟩ := admissible_bounds hd ht0 ht1 hk' hlk'
  set x := 1 + t * ((l : ℝ) - 1)
  set y := c + t * ((k : ℝ) - 1)
  have hy0 : 0 < y := by simp only [y]; nlinarith
  have hx0 : 0 < x := by simp only [x]; nlinarith
  constructor
  · -- `(x/y)^t ≥ (t/(c+t))^t (l/k)^t`.
    have hratio : t / (c + t) * ((l : ℝ) / k) ≤ x / y := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hy0]
      nlinarith [mul_le_mul_of_nonneg_left hyk (by positivity : (0 : ℝ) ≤ t * l)]
    have hpow : (t / (c + t)) ^ t * ((l : ℝ) / k) ^ t ≤ (x / y) ^ t := by
      rw [← mul_rpow (by positivity) (by positivity)]
      exact rpow_le_rpow (by positivity) hratio ht0.le
    have hle : α * ((l : ℝ) / k) ^ t ≤ replicaRatio d t k l := by
      calc α * ((l : ℝ) / k) ^ t = (1 - t) * ((t / (c + t)) ^ t * ((l : ℝ) / k) ^ t) := by
            simp only [α]; ring
        _ ≤ (1 - t) * (x / y) ^ t := mul_le_mul_of_nonneg_left hpow h1t.le
        _ ≤ _ := hw1
    have hinv : (max β α⁻¹)⁻¹ ≤ α := by
      rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (le_max_right _ _)) hα0]
      exact le_max_right _ _
    calc (max β α⁻¹)⁻¹ * ((l : ℝ) / k) ^ t ≤ α * ((l : ℝ) / k) ^ t :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ _ := hle
  · -- `r ≤ (x/y)^t/(1 - t) ≤ (1 + d)/(1 - t)`.
    have hxy' : x / y ≤ 1 + d := by rw [div_le_iff₀ hy0]; linarith
    have hpow : (x / y) ^ t ≤ 1 + d := by
      calc (x / y) ^ t ≤ (1 + d) ^ t := rpow_le_rpow (by positivity) hxy' ht0.le
        _ ≤ (1 + d) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) ht1.le
        _ = 1 + d := rpow_one _
    calc replicaRatio d t k l ≤ (x / y) ^ t / (1 - t) := hw2
      _ ≤ β := div_le_div_of_nonneg_right hpow h1t.le
      _ ≤ max β α⁻¹ := le_max_left _ _

/-- **Lemma 6.2, uniform convergence of the marked ratio** (`05-replicas.tex`,
lines 410–417): on the admissible range `1 ≤ k`, `1 ≤ l ≤ k + d`,
`|r(k, l) - max((l - d)/k, 0)^t| ≤ C k^(-t)`. The eigenvalue of the star operator on the
branch is `(l - d)/k`, so this is the scalar content of `‖R_{Q,k} - (J_{Q,k})_+^t‖ → 0`. -/
theorem exists_abs_replicaRatio_sub_le (hd : 0 < d) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C, ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k + d →
      |replicaRatio d t k l - (max (((l : ℝ) - d) / k) 0) ^ t| ≤ C * (k : ℝ) ^ (-t) := by
  set c := replicaConst d t
  have hc := one_le_replicaConst hd ht0.le
  have h1t : 0 < 1 - t := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set C1 := t * (1 + (1 + d) / (1 - t)) / t ^ t
  set C2 := (1 + (1 + d) * c) / t + d
  refine ⟨C1 + C2 ^ t, fun k l hk hl hlk => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlk' : (l : ℝ) ≤ k + d := by exact_mod_cast hlk
  obtain ⟨-, -, hw3⟩ := replicaRatio_wendel hd ht0 ht1 hk' hl'
  obtain ⟨hty, hxy, -, -⟩ := admissible_bounds hd ht0 ht1 hk' hlk'
  set x := 1 + t * ((l : ℝ) - 1)
  set y := c + t * ((k : ℝ) - 1)
  have hy0 : 0 < y := by simp only [y]; nlinarith
  have hx0 : 0 < x := by simp only [x]; nlinarith
  have hkt : (k : ℝ) ^ (-t) = ((k : ℝ) ^ t)⁻¹ := rpow_neg hk0.le t
  -- First term: `|r - (x/y)^t| ≤ C1 k^(-t)`.
  have hxy' : x / y ≤ 1 + d := by rw [div_le_iff₀ hy0]; linarith
  have hpow : (x / y) ^ t ≤ 1 + d := by
    calc (x / y) ^ t ≤ (1 + d) ^ t := rpow_le_rpow (by positivity) hxy' ht0.le
      _ ≤ (1 + d) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) ht1.le
      _ = 1 + d := rpow_one _
  have hyt : t ^ t * (k : ℝ) ^ t ≤ y ^ t := by
    rw [← mul_rpow ht0.le hk0.le]; exact rpow_le_rpow (by positivity) hty ht0.le
  have hT1 : |replicaRatio d t k l - (x / y) ^ t| ≤ C1 * (k : ℝ) ^ (-t) := by
    refine hw3.trans ?_
    rw [hkt]
    have hnum : t * (1 + (x / y) ^ t / (1 - t)) ≤ t * (1 + (1 + d) / (1 - t)) :=
      mul_le_mul_of_nonneg_left (by gcongr) ht0.le
    calc t * (1 + (x / y) ^ t / (1 - t)) / y ^ t
        ≤ t * (1 + (1 + d) / (1 - t)) / (t ^ t * (k : ℝ) ^ t) := by
          apply div_le_div₀ (by positivity) hnum (by positivity) hyt
      _ = C1 * ((k : ℝ) ^ t)⁻¹ := by simp only [C1]; field_simp
  -- Second term: `|(x/y)^t - target^t| ≤ |x/y - target|^t ≤ C2^t k^(-t)`.
  set τ := max (((l : ℝ) - d) / k) 0
  have hτ0 : 0 ≤ τ := le_max_right _ _
  have hlin : |x / y - τ| ≤ C2 / k := by
    have h1 : |x / y - l / k| ≤ (1 + (1 + d) * c) / t / k := by
      rw [div_sub_div _ _ hy0.ne' hk0.ne', abs_div, abs_of_pos (mul_pos hy0 hk0),
        div_le_div_iff₀ (mul_pos hy0 hk0) hk0]
      have hid : x * k - y * l = k * (1 - t) - l * (c - t) := by simp only [x, y]; ring
      rw [hid]
      have habs : |(k : ℝ) * (1 - t) - l * (c - t)| ≤ k * (1 + (1 + d) * c) := by
        have hl0 : (0 : ℝ) ≤ l := by linarith
        have hct : 0 ≤ c - t := by linarith
        have e1 : (l : ℝ) * (c - t) ≤ l * c := mul_le_mul_of_nonneg_left (by linarith) hl0
        have e2 : (l : ℝ) * c ≤ (k + d) * c := mul_le_mul_of_nonneg_right hlk' (by linarith)
        have e3 : (d : ℝ) * c ≤ k * d * c := by
          have : (d : ℝ) * c * 1 ≤ d * c * k := mul_le_mul_of_nonneg_left hk' (by positivity)
          linarith
        have e4 : 0 ≤ (l : ℝ) * (c - t) := mul_nonneg hl0 hct
        have e5 : 0 ≤ (k : ℝ) * t := by positivity
        have e6 : 0 ≤ (k : ℝ) * (1 + d) * c := by positivity
        rw [abs_le]; constructor <;> nlinarith
      calc |(k : ℝ) * (1 - t) - l * (c - t)| * k ≤ k * (1 + (1 + d) * c) * k :=
            mul_le_mul_of_nonneg_right habs hk0.le
        _ ≤ (1 + (1 + d) * c) / t * (y * k) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ ht0]
            have : 0 ≤ k * (1 + (1 + d) * c) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hty this]
    have h2 : |(l : ℝ) / k - τ| ≤ d / k := by
      simp only [τ]
      rcases le_total (((l : ℝ) - d) / k) 0 with h | h
      · rw [max_eq_right h, sub_zero, abs_of_nonneg (by positivity),
          div_le_div_iff_of_pos_right hk0]
        rw [div_le_iff₀ hk0, zero_mul] at h
        linarith
      · rw [max_eq_left h, ← sub_div, abs_div, abs_of_pos hk0, sub_sub_cancel, abs_of_nonneg
          (by linarith)]
    calc |x / y - τ| ≤ |x / y - l / k| + |(l : ℝ) / k - τ| := abs_sub_le _ _ _
      _ ≤ (1 + (1 + d) * c) / t / k + d / k := add_le_add h1 h2
      _ = C2 / k := by simp only [C2]; ring
  have hT2 : |(x / y) ^ t - τ ^ t| ≤ C2 ^ t * (k : ℝ) ^ (-t) := by
    refine (abs_rpow_sub_rpow_le (by positivity) hτ0 ht0.le ht1.le).trans ?_
    calc |x / y - τ| ^ t ≤ (C2 / k) ^ t := rpow_le_rpow (abs_nonneg _) hlin ht0.le
      _ = C2 ^ t * (k : ℝ) ^ (-t) := by
          rw [div_rpow (by positivity) hk0.le, hkt, div_eq_mul_inv]
  calc |replicaRatio d t k l - τ ^ t|
      ≤ |replicaRatio d t k l - (x / y) ^ t| + |(x / y) ^ t - τ ^ t| := abs_sub_le _ _ _
    _ ≤ C1 * (k : ℝ) ^ (-t) + C2 ^ t * (k : ℝ) ^ (-t) := add_le_add hT1 hT2
    _ = (C1 + C2 ^ t) * (k : ℝ) ^ (-t) := by ring

end Partition
