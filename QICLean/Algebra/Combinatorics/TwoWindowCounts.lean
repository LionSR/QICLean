/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic

/-!
# Counting frequency vectors with two prescribed coordinates

For an alphabet of `s + 3` labels, prescribing two distinct coordinates
leaves `s + 1` free coordinates. At residual total `m`, their number is
`(m + s).choose s`. At total `r` and prescribed values `i`, `j`, the count
is zero when `r < i + j`; otherwise it is `(r - i - j + s).choose s`.

These statements count all frequency vectors on the original alphabet.
They are supporting counting for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines 1324–1332.
The grouped alphabet there has two windows of `2 * ℓ` labels and three
bulk labels, hence `4 * ℓ + 3` labels.

For a polynomial degree bound `k`, a local dimension `d`, a window size `ℓ`
and a frequency bound `b`, the sum of the resulting two-window counting factors is bounded
by a product of powers. When `k ≥ 1`, `d ≥ 2`, `ℓ ≥ 1` and `b ≤ k`, that product
is at most `(d * k) ^ (17 * (ℓ + b))`. Every degree from zero through `k` is retained.

**Local fix (count):** The ordered-gap factors used in the sum estimate retain the
additional `+1` documented in the paper-gap note
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

## Main results

* `Nat.card_fun_sum_eq_and_two_eq_of_total`, `Nat.sum_card_fun_sum_eq_and_two_eq_le`.
* `Nat.two_window_rank_sum_le_factor`, `Nat.two_window_rank_factor_le_pow`.

## References

ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1332.

Moved from TNLean, `TNLean/Algebra/FrequencyCounts.lean` and
`TNLean/Algebra/TwoWindowRankBounds.lean` at commit `49b78ed821` (Apache-2.0).
-/

open scoped BigOperators

/-- Counting natural frequency vectors with two prescribed coordinates.
Supporting counting for ALVV, arXiv:1602.08828v2, eq:H-mid-cut, lines 810–821,
and prop:Cheby-AGSP-eff, lines 1324–1332. -/
theorem Nat.card_fun_sum_eq_and_two_eq
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (m i j : ℕ) :
    Nat.card {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} =
      (m + s).choose s := by
  classical
  let S : Finset I := (Finset.univ.erase u).erase v
  have hsum (α : I → ℕ) :
      (∑ a, α a) = (∑ a : S, α a) + α u + α v := by
    have h₁ := Finset.sum_erase_add (a := u) (Finset.univ : Finset I) α (by simp)
    have h₂ := Finset.sum_erase_add (a := v) (Finset.univ.erase u) α (by simp [huv.symm])
    rw [Finset.sum_coe_sort]
    dsimp only [S]
    omega
  let extend (β : S → ℕ) (a : I) : ℕ :=
    if hau : a = u then i else if hav : a = v then j
      else β ⟨a, by simp [S, hau, hav]⟩
  have hextu (β : S → ℕ) : extend β u = i := by simp [extend]
  have hextv (β : S → ℕ) : extend β v = j := by simp [extend, huv.symm]
  have hextS (β : S → ℕ) (a : S) : extend β a = β a := by
    simp only [extend,
      dite_eq_right (Finset.mem_erase.mp (Finset.mem_erase.mp a.property).2).1,
      dite_eq_right (Finset.mem_erase.mp a.property).1]
  let restrict : {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} →
      {β : S → ℕ // (∑ a, β a) = m} := fun α ↦ ⟨fun a ↦ α.val a, by
    have hα := hsum α.val
    have hp := α.property
    change (∑ a : S, α.val a) = m
    omega⟩
  let reinsert : {β : S → ℕ // (∑ a, β a) = m} →
      {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} :=
    fun β ↦ ⟨extend β.val, by
      refine ⟨?_, hextu β.val, hextv β.val⟩
      simpa only [hextS, hextu, hextv, β.property] using hsum (extend β.val)⟩
  let e : {α : I → ℕ // (∑ a, α a) = m + i + j ∧ α u = i ∧ α v = j} ≃
      {β : S → ℕ // (∑ a, β a) = m} :=
    { toFun := restrict
      invFun := reinsert
      left_inv := by
        intro α
        apply Subtype.ext
        funext a
        change extend (fun b : S ↦ α.val b) a = α.val a
        by_cases hau : a = u
        · simpa only [hau, hextu] using α.property.2.1.symm
        · by_cases hav : a = v
          · simpa only [hav, hextv] using α.property.2.2.symm
          · simp only [extend, dite_eq_right hau, dite_eq_right hav]
      right_inv := by
        intro β
        exact Subtype.ext (funext fun a ↦ hextS β.val a) }
  have hcardS : Fintype.card S = s + 1 := by
    rw [Fintype.card_coe, (show S = ((Finset.univ : Finset I).erase u).erase v from rfl),
      Finset.card_erase_of_mem (by simp [huv.symm] : v ∈ (Finset.univ : Finset I).erase u),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, hcard]
    omega
  rw [Nat.card_congr e]
  rw [Nat.card_congr (Sym.equivNatSumOfFintype S m).symm]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, hcardS]
  have hbase : s + 1 + m - 1 = m + s := by omega
  simpa only [hbase] using (Nat.choose_symm_add (a := m) (b := s))

/-- No natural frequency vector has total smaller than two prescribed
coordinates. This is the empty case of the counting used in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`prop:Cheby-AGSP-eff`, lines 1324–1332. -/
theorem Nat.card_fun_sum_eq_and_two_eq_of_lt
    {I : Type*} [Fintype I]
    (u v : I) (huv : u ≠ v) (r i j : ℕ) (hr : r < i + j) :
    Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} = 0 := by
  let : IsEmpty {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} :=
    ⟨fun α ↦ by
      have hpair := Finset.add_le_sum (s := Finset.univ) (f := α.val)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ u) (Finset.mem_univ v) huv
      have hle : i + j ≤ r := by
        simpa only [α.property.1, α.property.2.1, α.property.2.2] using hpair
      exact (not_le_of_gt hr) hle⟩
  exact Nat.card_of_isEmpty

/-- The number of natural frequency vectors of a fixed total with two fixed
coordinates. This auxiliary count applies to the grouped alphabet in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`prop:Cheby-AGSP-eff`, lines 1324–1332. It counts all frequency vectors,
without a further selection condition. -/
theorem Nat.card_fun_sum_eq_and_two_eq_of_total
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (r i j : ℕ) :
    Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} =
      if i + j ≤ r then (r - i - j + s).choose s else 0 := by
  split_ifs with hle
  · have hres : (r - i - j) + i + j = r := by omega
    simpa only [hres] using
      Nat.card_fun_sum_eq_and_two_eq hcard u v huv (r - i - j) i j
  · exact Nat.card_fun_sum_eq_and_two_eq_of_lt u v huv r i j (by omega)

/-- The number of frequency vectors with two prescribed coordinates is
bounded by a finite box. This is a full-alphabet counting bound for ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`prop:Cheby-AGSP-eff`, lines 1324–1332. For the two-window alphabet,
s = 4ℓ. No selection condition is imposed on the counted vectors. -/
theorem Nat.card_fun_sum_eq_and_two_eq_le
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (r i j : ℕ) :
    Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j} ≤
      (r + 1) ^ s := by
  rw [Nat.card_fun_sum_eq_and_two_eq_of_total hcard u v huv r i j]
  split_ifs
  · exact (Nat.choose_add_le_add_one_pow (r - i - j) s).trans
      (Nat.pow_le_pow_left
        (Nat.add_le_add_right ((Nat.sub_le (r - i) j).trans (Nat.sub_le r i)) 1) s)
  · exact Nat.zero_le _

/-- The complete frequency slices up to degree k, with two prescribed
coordinates, have total cardinality at most (k+1)^(s+1). This is the
full-alphabet degree summation in the rank argument of ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem Nat.sum_card_fun_sum_eq_and_two_eq_le
    {I : Type*} [Fintype I] {s : ℕ} (hcard : Fintype.card I = s + 3)
    (u v : I) (huv : u ≠ v) (k i j : ℕ) :
    (∑ r ∈ Finset.range (k + 1),
      Nat.card {α : I → ℕ // (∑ a, α a) = r ∧ α u = i ∧ α v = j}) ≤
        (k + 1) ^ (s + 1) := by
  calc
    _ ≤ ∑ r ∈ Finset.range (k + 1), (r + 1) ^ s :=
      Finset.sum_le_sum fun r _ ↦ Nat.card_fun_sum_eq_and_two_eq_le hcard u v huv r i j
    _ ≤ (k + 1) ^ (s + 1) := by
      simpa only [Finset.card_range, nsmul_eq_mul, Nat.cast_id, pow_succ, Nat.mul_comm] using
        Finset.sum_le_card_nsmul (Finset.range (k + 1))
          (fun r : ℕ ↦ (r + 1) ^ s) ((k + 1) ^ s)
          (fun r hr ↦ Nat.pow_le_pow_left (Nat.succ_le_of_lt (Finset.mem_range.mp hr)) s)

/-- A scalar bound for the rank factors in the two-window expansion.
This is an arithmetic auxiliary for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`,
lines 1324–1332. The parameter `b` is any upper bound for the two
selected frequencies with `b ≤ k`; its quotient formula is used only
when applying this estimate to the expansion. -/
theorem Nat.two_window_rank_factor_le_pow (k d ℓ b : ℕ)
    (hk : 1 ≤ k) (hd : 2 ≤ d) (hℓ : 1 ≤ ℓ) (hb : b ≤ k) :
    (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
      (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) ≤
      (d * k) ^ (17 * (ℓ + b)) := by
  have hdk : 2 * k ≤ d * k := Nat.mul_le_mul_right k hd
  have hbase : 2 ≤ d * k ∧ k + 1 ≤ d * k ∧ b + 1 ≤ d * k := by omega
  have hdX : d ≤ d * k := Nat.le_mul_of_pos_right d (by omega)
  have hℓX : 2 * ℓ ≤ (d * k) ^ ℓ :=
    (Nat.mul_le_pow (by decide : 2 ≠ 1) ℓ).trans (Nat.pow_le_pow_left hbase.1 ℓ)
  have hgap : 2 * (k + 1) ≤ (d * k) ^ 2 :=
    (Nat.mul_le_mul hbase.1 hbase.2.1).trans_eq (pow_two _).symm
  refine (Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hℓX 2) (Nat.pow_le_pow_left hbase.2.2 2))
        (Nat.pow_le_pow_left hbase.2.1 _))
      (Nat.pow_le_pow_left hgap _))
    (Nat.pow_le_pow_left hdX _)).trans ?_
  simp only [← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- A uniform bound for the sum of the two-window rank factors.
This is an arithmetic auxiliary for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`,
lines 1324–1332. Every degree from zero through `k` is retained;
the two ordered-gap binomial coefficients include their upper-argument
correction. -/
theorem Nat.two_window_rank_sum_le_factor (k d ℓ b : ℕ)
    (hd : 1 ≤ d) (hb : b ≤ k) :
    (2 * ℓ) ^ 2 *
      (∑ r ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (b + 1),
          ∑ j ∈ Finset.range (b + 1),
            (r + 1) ^ (4 * ℓ) *
              ((r + i + 1).choose (2 * i + 1) *
                (r + j + 1).choose (2 * j + 1) *
                d ^ (2 * (i + j) + 4 * ℓ))) ≤
      (2 * ℓ) ^ 2 * (b + 1) ^ 2 * (k + 1) ^ (4 * ℓ + 1) *
        (2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ) := by
  have hchoose (r i : ℕ) (hr : r ≤ k) (hi : i ≤ b) :
      (r + i + 1).choose (2 * i + 1) ≤ (2 * (k + 1)) ^ (2 * b + 1) :=
    (Nat.choose_le_pow _ _).trans
      ((Nat.pow_le_pow_left (by omega : r + i + 1 ≤ 2 * (k + 1)) _).trans
        (Nat.pow_le_pow_right (by omega : 0 < 2 * (k + 1)) (by omega)))
  have hgap (r i j : ℕ) (hr : r ≤ k) (hi : i ≤ b) (hj : j ≤ b) :
      (r + i + 1).choose (2 * i + 1) * (r + j + 1).choose (2 * j + 1) ≤
        (2 * (k + 1)) ^ (4 * b + 2) := by
    simpa only [← pow_add, show 2 * b + 1 + (2 * b + 1) = 4 * b + 2 by omega] using
      Nat.mul_le_mul (hchoose r i hr hi) (hchoose r j hr hj)
  let H := (k + 1) ^ (4 * ℓ) *
    ((2 * (k + 1)) ^ (4 * b + 2) * d ^ (4 * b + 4 * ℓ))
  have hterm (r i j : ℕ) (hr : r ≤ k) (hi : i ≤ b) (hj : j ≤ b) :
      (r + 1) ^ (4 * ℓ) *
        ((r + i + 1).choose (2 * i + 1) * (r + j + 1).choose (2 * j + 1) *
          d ^ (2 * (i + j) + 4 * ℓ)) ≤ H :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : r + 1 ≤ k + 1) _)
      (Nat.mul_le_mul (hgap r i j hr hi hj)
        (Nat.pow_le_pow_right (by omega : 0 < d) (by omega)))
  have hsum := Finset.sum_le_sum (s := Finset.range (k + 1)) fun r hr ↦
    Finset.sum_le_sum (s := Finset.range (b + 1)) fun i hi ↦
      Finset.sum_le_sum (s := Finset.range (b + 1)) fun j hj ↦
        hterm r i j (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul] at hsum
  refine (Nat.mul_le_mul_left ((2 * ℓ) ^ 2) hsum).trans_eq ?_
  simp only [H, pow_succ (k + 1) (4 * ℓ), pow_two (b + 1)]
  ac_rfl
