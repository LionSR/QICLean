/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Numerical coefficients in the rough and sharp lower comparisons

The explicit rough lower estimate implies the comparison with coefficient
three when the parameter is at most one half. The entropy parameter is
arbitrary; its positive part is retained in the defect term.

For a nonnegative entropy parameter and a parameter at most one, the same
explicit estimate at total weight `a K`, divided by the number of copies,
implies the comparison with coefficient four. The explicit sharp lower
estimate, summed over the bands, implies the sharp comparison with any
constant `C' ≥ 4` that dominates `25 C₀`.

These are scalar consequences used in the lower comparisons, rather than
assertions about a physical state or its energy defect.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, `comparator:rough-lower` and
`comparator:sharp-lower`, lines 153--196 and 585--651, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- The explicit rough lower expression dominates the expression with
coefficient three. No sign assumption is imposed on the entropy parameter.
Auxiliary to the area-law manuscript, `07-comparators.tex`,
`comparator:rough-lower`, lines 153--169 and 585--651. -/
theorem rough_lower_coefficient_three (S D h delta tau a : ℝ)
    (hD : 0 ≤ D) (hh : 0 ≤ h) (hdelta : 0 ≤ delta)
    (htau : 0 < tau) (ha : 0 < a) (haHalf : a ≤ 1 / 2) :
    4 * S - 2 * 3 * (tau * D + h / a) -
        3 * (delta / tau) * max 0 (2 * S) ≤
      2 * (2 * S - tau * (D + D) - (3 + 1 / a) * h -
        (delta / tau) * max 0 (2 * S)) := by
  have haInv : 2 ≤ 1 / a := (le_div_iff₀ ha).2 (by linarith only [haHalf])
  simp only [div_eq_mul_inv, one_mul] at haInv ⊢
  nlinarith only [mul_nonneg htau.le hD,
    mul_nonneg (by linarith only [haInv] : 0 ≤ 4 * a⁻¹ - 6) hh,
    mul_nonneg (mul_nonneg hdelta (inv_nonneg.mpr htau.le))
      (le_max_left 0 (2 * S))]

/-- The explicit rough lower estimate at per-band weight `a ≤ 1`, total weight `a K` and
nonnegative entropy parameter `S`, divided by the number `k` of copies, gives the rough lower
comparison with coefficient four. Auxiliary to the area-law manuscript, `07-comparators.tex`,
`comparator:rough-lower`, lines 162--169 and 585--651. -/
theorem rough_lower_coefficient_four_div (K a k S L h δ τ r Nlog : ℝ) (hK : 0 ≤ K) (ha : 0 < a)
    (ha1 : a ≤ 1) (hk : 0 < k) (hS : 0 ≤ S) (hL : 0 ≤ L) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hτ : 0 < τ)
    (hbound : 2 * (1 / 4) * K * (2 * (a / 2) * k *
      ((2 * S - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h) - δ / τ * max 0 (2 * S)) - r) ≤
        Nlog) :
    2 * (1 / 4) * (a * K) * (2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S) -
        (K / 2 * r) / k ≤ Nlog / k := by
  rw [max_eq_right (by linarith), show 1 / (2 * (a / 2)) = 1 / a by ring] at hbound
  rw [le_div_iff₀ hk]
  have hha : h ≤ h / a := le_div_self hh ha ha1
  have hcore : 2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S ≤
      2 * S - τ * (L + L) - (3 + 1 / a) * h - δ / τ * (2 * S) := by
    have hδS : 0 ≤ δ / τ * S := mul_nonneg (div_nonneg hδ hτ.le) hS
    have : (3 + 1 / a) * h = 3 * h + h / a := by ring
    nlinarith [mul_nonneg hτ.le hL]
  have hcoef : 0 ≤ 2 * (1 / 4) * (a * K) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcore hcoef
  have hexpand : (2 * (1 / 4) * (a * K) * (2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S) -
      K / 2 * r / k) * k = 2 * (1 / 4) * (a * K) *
        (2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S) * k - K / 2 * r := by
    field_simp
  rw [hexpand]
  have : 2 * (1 / 4) * K * (2 * (a / 2) * k *
      ((2 * S - τ * (L + L) - (3 + 1 / a) * h) - δ / τ * (2 * S)) - r) =
      2 * (1 / 4) * (a * K) * (2 * S - τ * (L + L) - (3 + 1 / a) * h - δ / τ * (2 * S)) * k -
        K / 2 * r := by ring
  nlinarith [mul_le_mul_of_nonneg_right hmul hk.le]

/-- The explicit sharp lower estimate, summed over the `K` bands and divided by the number `k`
of copies, gives the sharp lower comparison with a constant `C' ≥ 4` that also dominates the
moment coefficient, `25 C₀ ≤ C'`. Auxiliary to the area-law manuscript, `07-comparators.tex`,
`comparator:sharp-lower`, lines 171--196 and 550--651. -/
theorem sharp_lower_coefficient_div {K : ℕ} (a k S L τ h δ gm C₀ B C' r Nlog : ℝ) (A : Fin K → ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hk : 0 < k) (hS : 0 ≤ S) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hgm : 0 ≤ gm) (hB : 0 ≤ B) (hC'4 : 4 ≤ C')
    (hC'0 : 25 * C₀ ≤ C')
    (hbound : 2 * (1 / 4) * ∑ l, (2 * (a / 2) * k *
      ((2 * S + (1 - τ) * A l - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h -
        50 * (C₀ * B) * (a / 2)) - δ / τ * max 0 (2 * S + gm)) - r) ≤ Nlog) :
    2 * (1 / 4) * (a * K) * (2 * S + (1 - τ) * ((1 / (K : ℝ)) * ∑ l, A l) -
        C' * (τ * L + h / a + a * B) - C' * (δ / τ) * (S + gm)) - (K / 2 * r) / k ≤
      Nlog / k := by
  set P := 2 * (a / 2) * k with hP
  set X0 := 2 * S - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h - 50 * (C₀ * B) * (a / 2)
    with hX0
  set D0 := δ / τ * max 0 (2 * S + gm) with hD0
  have hsum : ∑ l, (P * ((2 * S + (1 - τ) * A l - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h -
        50 * (C₀ * B) * (a / 2)) - D0) - r) =
      K * (P * (X0 - D0) - r) + P * (1 - τ) * ∑ l, A l := by
    calc _ = ∑ l, ((P * (X0 - D0) - r) + P * (1 - τ) * A l) :=
          Finset.sum_congr rfl fun l _ ↦ by rw [hX0]; ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum] at hbound
  have havg : a * K * ((1 / (K : ℝ)) * ∑ l, A l) = a * ∑ l, A l := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · field_simp
  have hha : h ≤ h / a := le_div_self hh ha ha1
  have hcore : 2 * S - C' * (τ * L + h / a + a * B) - C' * (δ / τ) * (S + gm) ≤ X0 - D0 := by
    rw [hX0, hD0, max_eq_right (by linarith), show 1 / (2 * (a / 2)) = 1 / a by ring]
    have hδτ : 0 ≤ δ / τ := div_nonneg hδ hτ.le
    have h1 : δ / τ * (2 * S + gm) ≤ C' * (δ / τ) * (S + gm) := by
      have h0 : 2 * S + gm ≤ C' * (S + gm) := by nlinarith
      calc δ / τ * (2 * S + gm) ≤ δ / τ * (C' * (S + gm)) :=
            mul_le_mul_of_nonneg_left h0 hδτ
        _ = C' * (δ / τ) * (S + gm) := by ring
    have h2 : τ * (L + L) ≤ C' * (τ * L) := by nlinarith [mul_nonneg hτ.le hL]
    have h3 : (3 + 1 / a) * h ≤ C' * (h / a) := by
      have : (3 + 1 / a) * h = 3 * h + h / a := by ring
      nlinarith [div_nonneg hh ha.le]
    have h4 : 50 * (C₀ * B) * (a / 2) ≤ C' * (a * B) := by nlinarith [mul_nonneg ha.le hB]
    nlinarith
  rw [le_div_iff₀ hk]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hcoef : 0 ≤ 2 * (1 / 4) * (a * K) * k := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcore hcoef
  have hexpand : (2 * (1 / 4) * (a * K) * (2 * S + (1 - τ) * ((1 / (K : ℝ)) * ∑ l, A l) -
      C' * (τ * L + h / a + a * B) - C' * (δ / τ) * (S + gm)) - K / 2 * r / k) * k =
      2 * (1 / 4) * (a * K) * k * (2 * S - C' * (τ * L + h / a + a * B) -
        C' * (δ / τ) * (S + gm)) + 2 * (1 / 4) * (1 - τ) * k * (a * K * ((1 / (K : ℝ)) *
          ∑ l, A l)) - K / 2 * r := by
    rw [sub_mul, div_mul_cancel₀ _ hk.ne']
    ring
  rw [hexpand, havg]
  have hb : 2 * (1 / 4) * (K * (P * (X0 - D0) - r) + P * (1 - τ) * ∑ l, A l) =
      2 * (1 / 4) * (a * K) * k * (X0 - D0) + 2 * (1 / 4) * (1 - τ) * k * (a * ∑ l, A l) -
        K / 2 * r := by
    rw [hP]; ring
  linarith [hmul, hb, hbound]

end Real
