/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-!
# Explicit numerical estimates for the AKLV frequency sum

The binomial frequency sum is bounded by a power whose exponent is linear in the
window width and in the degree divided by that width. No operator or spectral
hypothesis enters these natural-number inequalities.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 651--663.
**Local fix (count):** The corrected exponent-tuple count is documented at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
-/

open scoped BigOperators

namespace Nat

private theorem aklv_frequency_term_le {q ell s r u k : ℕ}
    (hq : 1 ≤ q) (hr : r ≤ ell) (hu : u < s) (hk : k ≤ r / s) :
    (r - k + s).choose s * (r + k + 1).choose (2 * k + 1) *
        q ^ (2 * k + 2 * Nat.dist (u + 1) (s / 2)) ≤
      (q * (ell + 1)) ^ (3 * s + 6 * (ell / s) + 2) := by
  let B := q * (ell + 1)
  have hbase : ell + 1 ≤ B := by dsimp [B]; nlinarith
  have hqB : q ≤ B := by dsimp [B]; nlinarith
  have hB : 1 ≤ B := le_trans hq hqB
  have hkell : k ≤ ell := hk.trans ((Nat.div_le_self r s).trans hr)
  have hkdiv : k ≤ ell / s := hk.trans (Nat.div_le_div_right hr)
  have hdist : Nat.dist (u + 1) (s / 2) ≤ s := by
    rw [Nat.dist_eq_max_sub_min]
    have := Nat.div_le_self s 2
    omega
  have hfirst : (r - k + s).choose s ≤ B ^ s :=
    (Nat.choose_add_le_add_one_pow (r - k) s).trans
      (Nat.pow_le_pow_left (by omega : r - k + 1 ≤ B) s)
  have hsecond : (r + k + 1).choose (2 * k + 1) ≤ B ^ (4 * k + 2) := by
    calc
      _ ≤ (r + k + 1) ^ (2 * k + 1) := Nat.choose_le_pow _ _
      _ ≤ ((ell + 1) ^ 2) ^ (2 * k + 1) :=
        Nat.pow_le_pow_left (by nlinarith) _
      _ ≤ (B ^ 2) ^ (2 * k + 1) :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left hbase 2) _
      _ = B ^ (4 * k + 2) := by rw [← pow_mul]; congr 1; omega
  have hthird : q ^ (2 * k + 2 * Nat.dist (u + 1) (s / 2)) ≤ B ^ (2 * k + 2 * s) :=
    (Nat.pow_le_pow_left hqB _).trans
      (Nat.pow_le_pow_right hB (by omega))
  calc
    _ ≤ B ^ s * B ^ (4 * k + 2) * B ^ (2 * k + 2 * s) :=
      Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) hthird
    _ = B ^ (3 * s + 6 * k + 2) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ B ^ (3 * s + 6 * (ell / s) + 2) := Nat.pow_le_pow_right hB (by omega)

/-- The corrected AKLV frequency sum has a uniform explicit power bound for every degree
up to `ell`. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 651--663. -/
theorem aklv_frequency_sum_le {q ell s r : ℕ} (hq : 1 ≤ q)
    (hwidth : s ≤ ell + 1) (hr : r ≤ ell) :
    (∑ b : Fin s × Fin (r / s + 1),
      (r - b.2.val + s).choose s * (r + b.2.val + 1).choose (2 * b.2.val + 1) *
        q ^ (2 * b.2.val + 2 * Nat.dist (b.1.val + 1) (s / 2))) ≤
      (q * (ell + 1)) ^ (3 * s + 6 * (ell / s) + 4) := by
  let B := q * (ell + 1)
  let e := 3 * s + 6 * (ell / s) + 2
  have hbase : ell + 1 ≤ B := by dsimp [B]; nlinarith
  have hcount : s * (r / s + 1) ≤ B ^ 2 := by
    have := (Nat.div_le_self r s).trans hr
    have hsmall : s * (r / s + 1) ≤ (ell + 1) ^ 2 := by nlinarith
    exact hsmall.trans (Nat.pow_le_pow_left hbase 2)
  calc
    _ ≤ ∑ _b : Fin s × Fin (r / s + 1), B ^ e := by
      apply Finset.sum_le_sum
      intro b _
      exact aklv_frequency_term_le hq hr b.1.isLt (Nat.le_of_lt_succ b.2.isLt)
    _ = s * (r / s + 1) * B ^ e := by simp only [Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    _ ≤ B ^ 2 * B ^ e := Nat.mul_le_mul_right _ hcount
    _ = B ^ (3 * s + 6 * (ell / s) + 4) := by rw [← pow_add]; congr 1; dsimp [e]; omega

/-- A shorter window of width `min s (2 * sqrt ell)` has controlled width and exponent.
AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 658--663. -/
theorem aklv_effective_width_bounds {ell s : ℕ} (hell : 1 ≤ ell) (hs : 1 ≤ s) :
    let w := min s (2 * Nat.sqrt ell)
    1 ≤ w ∧ w ≤ ell + 1 ∧
      3 * w + 6 * (ell / w) + 5 ≤ 16 * (ell / s + Nat.sqrt ell + 1) := by
  have hn : 1 ≤ Nat.sqrt ell := Nat.sqrt_pos.mpr (by omega)
  have hsq := Nat.sqrt_le' ell
  have htwo := two_mul_le_add_sq (Nat.sqrt ell) (1 : ℕ)
  have hwidth : 2 * Nat.sqrt ell ≤ ell + 1 := by nlinarith
  dsimp only
  refine ⟨le_min hs (by omega), (min_le_right _ _).trans hwidth, ?_⟩
  by_cases h : s ≤ 2 * Nat.sqrt ell
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (by omega : 2 * Nat.sqrt ell ≤ s)]
    have hdiv : ell / (2 * Nat.sqrt ell) ≤ Nat.sqrt ell + 1 :=
      Nat.div_le_of_le_mul (by nlinarith [Nat.sqrt_le_add ell])
    calc
      _ ≤ 3 * (2 * Nat.sqrt ell) + 6 * (Nat.sqrt ell + 1) + 5 :=
        Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hdiv) (3 * (2 * Nat.sqrt ell))) 5
      _ ≤ 16 * (Nat.sqrt ell + 1) := by omega
      _ ≤ 16 * (ell / s + Nat.sqrt ell + 1) := Nat.mul_le_mul_left 16
        (by simpa only [Nat.add_assoc] using Nat.le_add_left (Nat.sqrt ell + 1) (ell / s))

end Nat
