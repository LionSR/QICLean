/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify

/-!
# Circular displacements in `ZMod n`

Arithmetic of the circular displacement `|a.valMinAbs|` of `a : ZMod n`, and of a cell
coordinate that advances by one under a group element. These are the spacing estimates of
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1654, for translations on a ring
of cells.

Moved from TNLean (`e113e005`): the arithmetic parts of
`TNLean/Lattice/TranslationSupercellSpacing.lean` and `TranslationFiniteOrbitSpacing.lean`.
-/

namespace ZMod

/-- Translation by the `k`-th power advances a cell coordinate by `k`.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem coordinate_pow_smul {V Γ : Type*} [Group Γ] [MulAction Γ V]
    {n : ℕ} (π : V → ZMod n) (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (k : ℕ) (v : V) : π (e ^ k • v) = π v + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, he, ih, Nat.cast_succ]; abel

/-- **Multiples of `q` reach far.** For `q ≥ 1` and residues `a`, `b` modulo `n`, some
`b + qt` lies at circular distance more than `n / 2 - q` from `a`. -/
theorem exists_lt_natAbs_valMinAbs_add {n : ℕ} [NeZero n] {q : ℕ} (hq : 0 < q)
    (a b : ZMod n) :
    ∃ t : ℕ, n / 2 < (b + ((q * t : ℕ) : ZMod n) - a).valMinAbs.natAbs + q := by
  have hn := NeZero.pos n
  set c := (b - a).val with hc
  have hcL : c < n := ZMod.val_lt (b - a)
  set h := n / 2 with hh
  have hhn : h ≤ n - h := by omega
  have hval (t : ℕ) : (b + ((q * t : ℕ) : ZMod n) - a).val = (q * t + c) % n := by
    rw [← ZMod.val_natCast, Nat.cast_add, hc, ZMod.natCast_zmod_val]
    congr 1
    abel
  simp only [ZMod.valMinAbs_natAbs_eq_min]
  by_cases hsmall : h < q
  · exact ⟨0, by omega⟩
  replace hsmall := not_lt.mp hsmall
  by_cases hch : c ≤ h
  · refine ⟨(h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (h - c) q
    have h2 := Nat.lt_div_mul_add (a := h - c) hq
    rw [mul_comm] at h1 h2
    rw [hval, Nat.mod_eq_of_lt (show q * ((h - c) / q) + c < n by omega)]
    omega
  · refine ⟨(n + h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (n + h - c) q
    have h2 := Nat.lt_div_mul_add (a := n + h - c) hq
    rw [mul_comm] at h1 h2
    set s := q * ((n + h - c) / q) + c
    have hs : s % n = s - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hval, hs]
    omega

/-- Every positive multiple up to `mL` carries a nearby coordinate at least `L/2` away.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem natAbs_valMinAbs_add_mul_ge_of_near {n L m : ℕ} [NeZero n]
    (hL : 0 < L) (hn : 2 * (m + 1) * L ≤ n)
    (a : ZMod n) (ha : a.valMinAbs.natAbs ≤ L / 2)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    L / 2 ≤ (a + ((k * L : ℕ) : ZMod n)).valMinAbs.natAbs := by
  rw [ZMod.valMinAbs_natAbs_eq_min] at ha ⊢
  have hm : 2 * (m * L) + 2 * L ≤ n := by nlinarith only [hn]
  have hav := ZMod.val_lt a
  have hkl : L ≤ k * L := by nlinarith
  have hku : k * L ≤ m * L := Nat.mul_le_mul_right L hkm
  have hhalf : 2 * (L / 2) ≤ L := Nat.mul_div_le L 2
  have hval : (a + ((k * L : ℕ) : ZMod n)).val = (a.val + k * L) % n := by
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  rw [hval]
  rcases min_le_iff.mp ha with ha | ha
  · rw [Nat.mod_eq_of_lt (by nlinarith : a.val + k * L < n)]
    apply le_min <;> omega
  · have hge : n ≤ a.val + k * L := by omega
    have hlt : a.val + k * L - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    apply le_min <;> omega

end ZMod
