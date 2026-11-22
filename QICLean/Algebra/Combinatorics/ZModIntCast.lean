/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic

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
