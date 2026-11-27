/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Prod

/-!
# Integer equality below a cyclic modulus

A nonzero multiple of a modulus has absolute value at least that modulus. Consequently,
projecting two integers whose difference is smaller than the modulus to `ZMod n` cannot identify
them. No positivity or finiteness assumption on the cyclic quotient is needed beyond the stated
bound on their difference.

Moved from TNLean, `TNLean/Algebra/ZModSmallDifference.lean` at commit `49b78ed821`
(Apache-2.0).

## Main results

* `ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt`
* `ZMod.intCast_ne_intCast_of_natAbs_sub_lt`

Moved from TNLean, `TNLean/MPS/FundamentalTheorem/OperatorGroup/AssociatorToolkit.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

namespace ZMod

/-- If the absolute integer difference is smaller than the modulus, equality
after projection to the cyclic quotient is equality of the original integers. -/
theorem intCast_eq_intCast_iff_of_natAbs_sub_lt {n : ℕ} (a b : ℤ)
    (hd : (b - a).natAbs < n) : (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · intro h
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hd)
    exact (sub_eq_zero.mp hz).symm
  · rintro rfl
    simp

/-- Distinct integers whose absolute difference is smaller than the modulus stay distinct
after projection to the cyclic quotient. -/
theorem intCast_ne_intCast_of_natAbs_sub_lt {n : ℕ} (a b : ℤ)
    (hd : (b - a).natAbs < n) (hab : a ≠ b) : (a : ZMod n) ≠ (b : ZMod n) :=
  mt (intCast_eq_intCast_iff_of_natAbs_sub_lt a b hd).mp hab

end ZMod


/-!
## Sparse residue classes of a finite set of integer pairs

For a finite set `F` of pairs of integers and a modulus `m ≥ 1`, the `m` residue classes of
the first coordinate partition `F`, so one of them contains at most `|F| / m` members of `F`;
the same holds for the second coordinate. The members of `F` whose first coordinate lies in
the first chosen class or whose second coordinate lies in the second are therefore at most
`2 |F| / m`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 11, `geometry:belt-count`, lines 210–237. Independently proved from the manuscript; no
upstream Lean proof text is reused.
-/

namespace Finset

/-- For a finite set `F` of pairs of integers and `m ≥ 1` there are residues `a, b` modulo `m`
such that at most `2 |F| / m` members `z` of `F` have `z.1 ≡ a` or `z.2 ≡ b` modulo `m`.
The statement is written without division, as `m * card ≤ 2 * |F|`; the empty set and `m = 1`
are included. Two-dimensional area law, Section 11, `geometry:belt-count`, lines 210–237. -/
theorem exists_mul_card_filter_emod_or_emod_le (F : Finset (ℤ × ℤ)) (m : ℕ) (hm : 0 < m) :
    ∃ a b : Fin m,
      m * (F.filter fun z ↦
        z.1 % (m : ℤ) = (a.val : ℤ) ∨ z.2 % (m : ℤ) = (b.val : ℤ)).card ≤
          2 * F.card := by
  have small_fiber (f : ℤ × ℤ → Fin m) :
      ∃ a, m * (F.filter fun z ↦ f z = a).card ≤ F.card := by
    by_contra! hcon
    have hle : ∀ a ∈ (Finset.univ : Finset (Fin m)),
        F.card / m + 1 ≤ (F.filter fun z ↦ f z = a).card := fun a _ ↦
      Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hm).mpr (by rw [Nat.mul_comm]; exact hcon a))
    have hsum := Finset.card_nsmul_le_sum _ _ _ hle
    rw [← Finset.card_eq_sum_card_fiberwise (fun z _ ↦ Finset.mem_univ (f z)),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    exact absurd hsum (Nat.not_le.mpr (Nat.lt_mul_div_succ F.card hm))
  let residue (x : ℤ) : Fin m :=
    ⟨(x % (m : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hm.ne'))).mpr
        (Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hm))⟩
  have residue_val (x : ℤ) : ((residue x).val : ℤ) = x % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hm.ne'))
  obtain ⟨a, ha⟩ := small_fiber (fun z ↦ residue z.1)
  obtain ⟨b, hb⟩ := small_fiber (fun z ↦ residue z.2)
  simp only [Fin.ext_iff, ← Int.natCast_inj, residue_val] at ha hb
  refine ⟨a, b, ?_⟩
  rw [Finset.filter_or]
  exact (Nat.mul_le_mul_left m (Finset.card_union_le _ _)).trans
    (by simpa only [Nat.mul_add, two_mul] using Nat.add_le_add ha hb)

end Finset

section


namespace Multiplicative

/-- A statement about every element of `ℤ₂`, written multiplicatively, follows from its
two instances. -/
theorem forall_zmod_two {P : Multiplicative (ZMod 2) → Prop}
    (h0 : P (ofAdd 0)) (h1 : P (ofAdd 1)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1]

/-- A statement about every element of `ℤ₂ × ℤ₂`, written multiplicatively, follows from its
four instances. -/
theorem forall_zmod_two_prod {P : Multiplicative (ZMod 2 × ZMod 2) → Prop}
    (h00 : P (ofAdd (0, 0))) (h01 : P (ofAdd (0, 1))) (h10 : P (ofAdd (1, 0)))
    (h11 : P (ofAdd (1, 1))) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h00, h01, h10, h11]

/-- A statement about every element of `ℤ₃`, written multiplicatively, follows from its
three instances. -/
theorem forall_zmod_three {P : Multiplicative (ZMod 3) → Prop}
    (h0 : P (ofAdd 0)) (h1 : P (ofAdd 1)) (h2 : P (ofAdd 2)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1, h2]

end Multiplicative

end
