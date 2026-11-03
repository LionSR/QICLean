/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Full short-block dimensions in the viable-tree count profile

The full space on at most four window lengths fits the common
polynomial node count. This is a numerical auxiliary for block-leaf
initialization in ALVV, arXiv:1602.08828v2, lines 1650–1662.
It does not assert a dimension bound for arbitrary long regions.
-/

namespace Nat

/-- The full short-block dimension fits the common powered-node count. -/
theorem viable_tree_leaf_count_le {q m ell s : ℕ}
    (hqm : q ≤ m) (hm : 2 ≤ m) (hell : 1 ≤ ell) (hs : 1 ≤ s) :
    q ^ (4 * ell) ≤ ((m * ell ^ 2) ^ (22 * ell)) ^ 6 * s ^ 3 := by
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell hell
  have hmBase : m ≤ m * ell ^ 2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left m hell2
  have hbase : 2 ≤ m * ell ^ 2 := hm.trans hmBase
  calc
    q ^ (4 * ell) ≤ (m * ell ^ 2) ^ (4 * ell) :=
      Nat.pow_le_pow_left (hqm.trans hmBase) _
    _ ≤ (m * ell ^ 2) ^ ((22 * ell) * 6) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    _ = ((m * ell ^ 2) ^ (22 * ell)) ^ 6 := pow_mul (m * ell ^ 2) (22 * ell) 6
    _ ≤ ((m * ell ^ 2) ^ (22 * ell)) ^ 6 * s ^ 3 := by
      simpa only [mul_one] using Nat.mul_le_mul_left
        (((m * ell ^ 2) ^ (22 * ell)) ^ 6) (Nat.one_le_pow 3 s hs)

end Nat
